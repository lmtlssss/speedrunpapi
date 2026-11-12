"""Independent proof replay for colony.lut-sqrt.v1 (integer square root and hypotenuse).

Claim (sqrt): out = floor(sqrt(a)) for every 2m-bit a.
Claim (hyp):  out = floor(sqrt((a*a + b*b) mod 2^(2n))) for every n-bit a, b.

Recurrence.  X_k = top 2k bits of the radicand, Q_k = root bits so far, r_k the signed remainder,
s = [r < 0], pair = next two bits:
    r' = 4r + pair + 3 + 4 * sum_j 2^j (q_j xnor s)        (mod 2^(k+2), two's complement)
    q' = [r' >= 0]
For s = 0 the added term is -(4Q+1); for s = 1 it is +(4Q+3).  Both give r' = X' - (2Q+1)^2, so
    r >= 0  =>  r = X - Q^2,          r < 0  =>  r = X - (Q+1)^2,          -(2Q+1) <= r <= 2Q
is kept by every row; hence Q^2 <= X < (Q+1)^2 after the last row.  |r'| < 2^(k+1) fits k+2 bits.

This program checks that the netlist is that recurrence.  Per row it rebuilds, from the netlist,
the polynomial of sum 2^c r'_c over the row's operand wires (mod 2^(k+2)) and compares it with the
right-hand side above.  The last row builds only carries; each of its LUTs is compared with the
truth table the carry definition gives.  For the hypotenuse the radicand word is first proved to be
(a*a + b*b) mod 2^(2n) by the block replay of independent_mul_checker.
"""
import argparse
import hashlib
import json
from pathlib import Path

from independent_mul_checker import parse_blif, lut_poly, atom_poly, BitPoly, replay


def pmul(p, q, mod):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = m1 | m2
            v = (out.get(m, 0) + c1 * c2) % mod
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    return out


def padd(acc, p, k, mod):
    for m, c in p.items():
        v = (acc.get(m, 0) + k * c) % mod
        if v:
            acc[m] = v
        else:
            acc.pop(m, None)


def xnor_poly(q, s, mod):
    """1 - q - s + 2qs for atoms q, s (None = 0)."""
    out = {frozenset(): 1}
    pq, ps = atom_poly(q), atom_poly(s)
    padd(out, pq, -1, mod)
    padd(out, ps, -1, mod)
    padd(out, pmul(pq, ps, mod), 2, mod)
    return out


def aeval(a, env):
    if a is None:
        return 0
    if a == 1:
        return 1
    return 1 - env[a[1:]] if a.startswith("!") else env[a]


def avars(a):
    return [] if a is None or a == 1 else [a.lstrip("!")]


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-sqrt.v1" or cert.get("kind") not in ("sqrt", "hyp"):
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        m, kind = cert["m"], cert["kind"]
        inputs, outputs, tables = parse_blif(raw)
        polys = {o: lut_poly(ins, onset) for o, (ins, onset) in tables.items()}
        used = set()
        if kind == "sqrt":
            oname = "asqrt"
            if inputs != ["a[%d]" % i for i in range(2 * m)]:
                return {"ok": False, "reason": "interface"}
            x = list(inputs)
        else:
            oname = "hypotenuse"
            if inputs != ["a[%d]" % i for i in range(m)] + ["b[%d]" % i for i in range(m)]:
                return {"ok": False, "reason": "interface"}
            words = {"A": ["a[%d]" % i for i in range(m)], "B": ["b[%d]" % i for i in range(m)]}
            blocks = cert["blocks"]
            err = replay(polys, words, blocks, used, modular=blocks[-1]["id"])
            if err:
                return err
            last = blocks[-1]
            a, b = ("A", 0, m), ("B", 0, m)
            if last["width"] != 2 * m or replay.values[last["id"]] != {(a, a): 1, (b, b): 1}:
                return {"ok": False, "reason": "radicand is not a*a + b*b mod 2^(2n)"}
            x = words[last["id"]]
        if outputs != ["%s[%d]" % (oname, i) for i in range(m)] or len(cert["rows"]) != m:
            return {"ok": False, "reason": "interface"}
        r, s, qit = [], None, []
        for k in range(1, m + 1):
            row = cert["rows"][k - 1]
            i, w = m - k, k + 2
            mod = 1 << w
            qname = "%s[%d]" % (oname, m - k)
            out, luts = row["out"], row["luts"]
            if len(out) != w or out[w - 1] != "!" + qname or any(n in used or n not in polys for n in luts) or len(set(luts)) != len(luts):
                return {"ok": False, "reason": "row %d shape" % k}
            qbit = lambda j: qit[k - 2 - j] if 0 <= k - 2 - j < len(qit) else None
            rbit = lambda c: r[c - 2] if c - 2 < len(r) else None
            if k < m:
                expect = {frozenset(): 3 % mod}
                padd(expect, atom_poly(x[2 * i]), 1, mod)
                padd(expect, atom_poly(x[2 * i + 1]), 2, mod)
                for c in range(2, w):
                    padd(expect, atom_poly(rbit(c)), 1 << c, mod)
                    padd(expect, xnor_poly(qbit(c - 2), s, mod), 1 << c, mod)
                got = BitPoly(mod)
                for c, a in enumerate(out):
                    for mono, kk in atom_poly(a).items():
                        got.add(mono, kk << c)
                for name in reversed(luts):
                    got.substitute(name, polys[name])
                    if len(got.terms) > 4096 * w:
                        return {"ok": False, "reason": "row %d: polynomial does not close" % k}
                if got.terms != expect:
                    return {"ok": False, "reason": "row %d is not the recurrence" % k}
            else:
                cols = {0: [x[2 * i], 1], 1: [x[2 * i + 1], 1]}
                for c in range(2, w):
                    cols[c] = [("r", rbit(c)), ("x", qbit(c - 2), s)]
                def col_vars(c):
                    vs = []
                    for a in cols[c]:
                        parts = [a] if not isinstance(a, tuple) else list(a[1:])
                        for p in parts:
                            vs += avars(p)
                    return vs
                def col_sum(c, env):
                    t = 0
                    for a in cols[c]:
                        if not isinstance(a, tuple):
                            t += aeval(a, env)
                        elif a[0] == "r":
                            t += aeval(a[1], env)
                        else:
                            t += 1 ^ aeval(a[1], env) ^ aeval(a[2], env)
                    return t
                c, cin = 0, None
                for name in luts:
                    ins, onset = tables[name]
                    group = []
                    while c < w and all(v in ins for v in col_vars(c)):
                        group.append(c)
                        c += 1
                    need = set(v for g in group for v in col_vars(g)) | ({cin} if cin else set())
                    if not group or need != set(ins):
                        return {"ok": False, "reason": "row %d: carry group" % k}
                    done = c == w
                    for rowbits in range(1 << len(ins)):
                        env = {v: (rowbits >> t) & 1 for t, v in enumerate(ins)}
                        tot = (env[cin] if cin else 0) + sum(col_sum(g, env) << t for t, g in enumerate(group))
                        want = ((tot >> (len(group) - 1)) & 1) ^ 1 if done else (tot >> len(group)) & 1
                        bits = "".join("1" if env[v] else "0" for v in ins)
                        if (bits in onset) != bool(want):
                            return {"ok": False, "reason": "row %d: carry table of %s" % (k, name)}
                    cin = name
                if c != w or cin != qname:
                    return {"ok": False, "reason": "row %d: carry chain does not end in the root bit" % k}
            used.update(luts)
            r, s = out, out[w - 1]
            qit.append(qname)
        if used != set(tables):
            return {"ok": False, "reason": "netlist has logic outside the derivation"}
        lev = {v: 0 for v in inputs}
        for o, (ins, _) in tables.items():
            if any(v not in lev for v in ins):
                return {"ok": False, "reason": "netlist order"}
            lev[o] = 1 + max([lev[v] for v in ins] + [0])
        if len(tables) != cert["lut_count"] or max(lev.values()) != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "kind": kind, "m": m, "lut_count": len(tables), "levels": max(lev.values()),
                "netlist_digest": cert["netlist_digest"],
                "proof": "each row equals the non-restoring recurrence (polynomial identity mod 2^(k+2)); recurrence lemma in the header"}
    except Exception as exc:
        return {"ok": False, "reason": "replay exception: " + type(exc).__name__ + ": " + str(exc)[:160]}


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--netlist", type=Path, required=True)
    p.add_argument("--derivation", type=Path, required=True)
    a = p.parse_args()
    res = verify(a.netlist.read_bytes(), json.loads(a.derivation.read_text()))
    print(json.dumps(res, sort_keys=True))
    raise SystemExit(0 if res["ok"] else 1)
