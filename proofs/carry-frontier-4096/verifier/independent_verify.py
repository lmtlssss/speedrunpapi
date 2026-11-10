"""Independent mathematical replay for bounded Colony transformations.

This checker never imports proposal/optimization code and derives claims from
original source, exact bit identities, and exact rational algebra.
"""
import hashlib
import json
from fractions import Fraction


def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256(raw):
    return "sha256:" + hashlib.sha256(raw).hexdigest()



CARRY_CONTRACT = "For all low prefixes and all high suffixes, preserve the high (width-cut) result bits of each independent unsigned modular addition; low result bits are excluded."
GF2_CONTRACT = "For all GF(2) input bitvectors, factor the specified linear map with minimum intermediate dimension equal to exact binary rank."
AFFINE_CONTRACT = "For all rational initial states, retain exact final affine state and chronological total affine cost, including all transported cross terms."
COMPOSE_CONTRACT = "For all low prefixes, preserve only the declared GF(2) projection of the incoming carry vector; unobserved high arithmetic outputs are excluded."

def gf2_rank(columns):
    basis = {}
    for col in columns:
        x = col
        for p in sorted(basis, reverse=True):
            if x >> p & 1:
                x ^= basis[p]
        if x:
            basis[x.bit_length() - 1] = x
    return len(basis)


def verify_carry(a, result):
    w, k, offs = a["width"], a["cut"], a["offsets"]
    if type(w) is not int or type(k) is not int or not 2 <= w <= 20 or not 1 <= k <= min(12, w - 1):
        return False
    if not isinstance(offs, list) or not 1 <= len(offs) <= 64 or any(type(c) is not int or not 0 <= c < 1 << w for c in offs):
        return False
    frontier = result["retained_state"]
    if frontier["cut"] != k or frontier["width"] != w or frontier["original_prefix_count"] != (1 << k):
        return False
    # Reconstruct every lower-prefix equivalence class directly from original arithmetic.
    groups = {}
    lowmask = (1 << k) - 1
    for p in range(1 << k):
        carries = []
        for c in offs:
            full = p + c
            lo = (p + (c & lowmask)) & lowmask
            incoming = ((p + (c & lowmask)) - lo) // (1 << k)
            if incoming not in (0, 1):
                return False
            # The identity below holds for EVERY high suffix h by distributivity.
            # p + 2^k*h + c == lo + 2^k*(h + (c>>k) + incoming)
            if full != lo + (1 << k) * ((c >> k) + incoming):
                return False
            carries.append(incoming)
        key = tuple(carries)
        groups.setdefault(key, []).append(p)
    expected = [{"incoming": list(q), "prefix_count": len(ps), "representative_low": ps[0]}
                for q, ps in sorted(groups.items())]
    return (set(result) == {"contract", "side_conditions", "retained_state", "recovery"} and
            result["contract"] == CARRY_CONTRACT and
            result["side_conditions"] == ["0 <= x < 2^width", "unsigned modular addition", "0 < cut < width", "offsets are fixed width-bit unsigned values"] and
            result["recovery"] == "For each offset o and high suffix h: high_bits=(h + (o>>cut) + incoming[o]) mod 2^(width-cut)." and
            set(frontier) == {"cut", "width", "states", "original_prefix_count", "retained_state_count"} and
            frontier["states"] == expected and frontier["retained_state_count"] == len(expected))


def verify_gf2(a, result):
    n, rows = a["n_inputs"], a["rows"]
    if type(n) is not int or not 1 <= n <= 128 or not isinstance(rows, list) or not 1 <= len(rows) <= 128 or any(type(r) is not int or not 0 <= r < 1 << n for r in rows):
        return False
    columns = [sum(((r >> j) & 1) << i for i, r in enumerate(rows)) for j in range(n)]
    B, C = result["basis_columns"], result["intermediate_masks"]
    if not isinstance(B, list) or not isinstance(C, list) or len(B) != len(C) or len(B) != result["rank"]:
        return False
    if any(type(x) is not int or x not in columns for x in B) or any(type(x) is not int or x < 0 or x >= 1 << n for x in C):
        return False
    if result["rank"] != gf2_rank(columns) or gf2_rank(B) != len(B):
        return False
    # Reconstruct entire matrix column-by-column. Linearity proves all input bitvectors.
    for j, original in enumerate(columns):
        output = 0
        for i, basis in enumerate(B):
            if C[i] >> j & 1:
                output ^= basis
        if output != original:
            return False
    return (set(result) == {"contract", "side_conditions", "rank", "original_columns", "basis_columns", "intermediate_masks", "original_matrix_rows"} and
            result["contract"] == GF2_CONTRACT and result["side_conditions"] == ["all operations over GF(2)", "input width as declared", "bit-independent linear map"] and
            result["original_columns"] == n and result["original_matrix_rows"] == len(rows))


def rational(s):
    return Fraction(str(s))


def verify_affine(a, result):
    steps = a["steps"]
    if not isinstance(steps, list) or not 1 <= len(steps) <= 256 or len(result["stage_cross_terms"]) != len(steps):
        return False
    state = [Fraction(1), Fraction(0)]
    cost = [Fraction(0), Fraction(0)]
    for i, step in enumerate(steps):
        if set(step) != {"a", "b", "c", "d"}:
            return False
        A, B, C, D = [rational(step[name]) for name in ("a", "b", "c", "d")]
        if rational(result["stage_cross_terms"][i]) != C * state[1]:
            return False
        # Independent symbolic polynomial composition in the variable initial_state.
        next_state = [A * state[0], A * state[1] + B]
        cost = [cost[0] + C * state[0], cost[1] + C * state[1] + D]
        state = next_state
    return (set(result) == {"contract", "side_conditions", "final_state", "total_cost", "stage_cross_terms", "step_count"} and
            result["contract"] == AFFINE_CONTRACT and result["side_conditions"] == ["rational exact affine state and cost", "all stages applied in supplied order"] and
            rational(result["final_state"]["a"]) == state[0] and
            rational(result["final_state"]["b"]) == state[1] and
            rational(result["total_cost"]["c"]) == cost[0] and
            rational(result["total_cost"]["d"]) == cost[1] and
            result["step_count"] == len(steps))


def verify_composed(a, result):
    arg_carry = a["carry"]
    project = a["project_rows"]
    m = len(arg_carry["offsets"])
    if not verify_carry(arg_carry, {"contract": CARRY_CONTRACT,
                    "side_conditions": ["0 <= x < 2^width", "unsigned modular addition", "0 < cut < width", "offsets are fixed width-bit unsigned values"],
                    "recovery": "For each offset o and high suffix h: high_bits=(h + (o>>cut) + incoming[o]) mod 2^(width-cut).",
                    "retained_state": result["frontier"]}):
        return False
    if not verify_gf2({"n_inputs": m, "rows": project}, result["projection"]):
        return False
    counts = {}
    for state in result["frontier"]["states"]:
        mask = sum(b << i for i, b in enumerate(state["incoming"]))
        observed = tuple(bin(r & mask).count("1") % 2 for r in project)
        counts[observed] = counts.get(observed, 0) + state["prefix_count"]
    want = [{"bits": list(k), "prefix_count": n} for k, n in sorted(counts.items())]
    return (set(result) == {"contract", "side_conditions", "frontier", "projection", "projected_classes", "projected_state_count"} and
            result["contract"] == COMPOSE_CONTRACT and
            result["side_conditions"] == ["bounded unsigned addition", "fixed GF(2) projection", "all original lower-prefix inputs included"] and
            result["projected_classes"] == want and result["projected_state_count"] == len(want))


CHECKERS = {"carry.frontier.v1": verify_carry, "gf2.rank-factor.v1": verify_gf2,
            "affine.cost-compose.v1": verify_affine,
            "carry.gf2-projection.v1": verify_composed}


def verify_package(raw, pkg):
    try:
        if type(pkg) is not dict or pkg["schema"] != "colony.math-transform.v1":
            return {"ok": False, "reason": "invalid package"}
        if pkg["source_digest"] != sha256(raw):
            return {"ok": False, "reason": "original source bytes changed"}
        if pkg.get("verdict") != "Candidate":
            return {"ok": False, "reason": "no candidate"}
        source = json.loads(raw.decode("utf-8"))
        name = source["operator"]
        if name != pkg["operator"] or name not in CHECKERS:
            return {"ok": False, "reason": "operator mismatch"}
        result = pkg["candidate"]
        if sha256(canon(result)) != pkg["candidate_digest"] or result["contract"] != pkg["claim_scope"]:
            return {"ok": False, "reason": "candidate digest or contract changed"}
        accepted = CHECKERS[name](source["args"], result)
        return {"ok": bool(accepted), "reason": "algebraic replay" if accepted else "invalid mathematical claim",
                "verifier": "colony.math-independent.v1"}
    except (ValueError, TypeError, IndexError, KeyError, ZeroDivisionError, OverflowError):
        return {"ok": False, "reason": "invalid or unsupported semantics"}


def main():
    import argparse
    from pathlib import Path
    p = argparse.ArgumentParser()
    p.add_argument("--source", required=True)
    p.add_argument("--proof", required=True)
    args = p.parse_args()
    result = verify_package(Path(args.source).read_bytes(), json.loads(Path(args.proof).read_text()))
    print(json.dumps(result, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
