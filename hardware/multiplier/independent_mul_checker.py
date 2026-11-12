"""Independent proof replay for colony.lut-mul.v1.  Shares no code with the compiler.

Claim: for all inputs, sum(2^c * out[c]) = a*b (or a*a).

The derivation only names blocks: which LUTs belong together, which earlier words a block
reads, and the word-level expression it computes.  Everything else is recomputed here.

Per block, from the netlist alone:
  1. sum(2^c out_c) is written as a polynomial in the block's LUT outputs and each LUT is replaced
     by the polynomial of its truth table, last LUT first, with coefficients mod 2^width.
     What remains must contain only wires of the declared operands and must equal the declared
     expression expanded over those wires.  So  out = expr(operands)  (mod 2^width)  for every
     assignment of the operand wires.
  2. The expression is carried as an integer polynomial in word variables.  Its range over the
     variables' boxes must lie in [0, 2^width).  A width-bit word congruent to a value in that
     range equals it.
The last block's word is the output vector and its polynomial must be exactly a*b.
"""
import argparse
import hashlib
import json
from pathlib import Path


def parse_blif(raw):
    text = raw.decode("ascii").replace("\\\n", " ")
    inputs, outputs, tables, cur = [], [], {}, None
    for line in text.splitlines():
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] == ".inputs":
            inputs += t[1:]
        elif t[0] == ".outputs":
            outputs += t[1:]
        elif t[0] == ".names":
            cur = t[-1]
            if cur in tables:
                raise ValueError("wire driven twice: " + cur)
            if len(t) - 2 > 6:
                raise ValueError("fan-in above 6: " + cur)
            tables[cur] = (t[1:-1], set())
        elif t[0] == ".model":
            pass
        elif t[0] == ".end":
            cur = None
        elif t[0].startswith("."):
            raise ValueError("unsupported BLIF construct " + t[0])
        else:
            if cur is None:
                raise ValueError("row outside a table")
            ins = tables[cur][0]
            if len(ins) == 0:
                if t != ["1"]:
                    raise ValueError("constant row")
                tables[cur][1].add("")
            elif len(t) != 2 or t[1] != "1" or len(t[0]) != len(ins) or set(t[0]) - {"0", "1"}:
                raise ValueError("only complete on-set minterm rows are accepted")
            else:
                tables[cur][1].add(t[0])
    return inputs, outputs, tables


def lut_poly(ins, onset):
    """Multilinear integer polynomial of a truth table (Moebius transform)."""
    k = len(ins)
    arr = [0] * (1 << k)
    for row in onset:
        arr[sum(1 << i for i, ch in enumerate(row) if ch == "1")] = 1
    for i in range(k):
        bit = 1 << i
        for r in range(1 << k):
            if r & bit:
                arr[r] -= arr[r ^ bit]
    return {frozenset(ins[i] for i in range(k) if (r >> i) & 1): c for r, c in enumerate(arr) if c}


def atom_poly(a):
    if a is None:
        return {}
    if a == 1:
        return {frozenset(): 1}
    if not isinstance(a, str):
        raise ValueError("atom")
    if a.startswith("!"):
        return {frozenset(): 1, frozenset([a[1:]]): -1}
    return {frozenset([a]): 1}


class BitPoly:
    """Multilinear polynomial over wires, coefficients mod m, indexed by wire."""

    def __init__(self, mod):
        self.mod, self.terms, self.index = mod, {}, {}

    def add(self, mono, c):
        c %= self.mod
        if not c:
            return
        v = (self.terms.get(mono, 0) + c) % self.mod
        if v:
            if mono not in self.terms:
                for w in mono:
                    self.index.setdefault(w, set()).add(mono)
            self.terms[mono] = v
        elif mono in self.terms:
            del self.terms[mono]
            for w in mono:
                self.index[w].discard(mono)

    def substitute(self, wire, poly):
        monos = list(self.index.get(wire, ()))
        for mono in monos:
            c = self.terms.pop(mono)
            for w in mono:
                self.index[w].discard(mono)
            rest = mono - {wire}
            for t, k in poly.items():
                self.add(rest | t, c * k)
        self.index.pop(wire, None)


def word_bits(atoms):
    """sum 2^i atom_i as {mono: coeff}."""
    out = {}
    for i, a in enumerate(atoms):
        for mono, c in atom_poly(a).items():
            out[mono] = out.get(mono, 0) + (c << i)
    return out


def bit_mul(p, q, mod):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = m1 | m2
            out[m] = (out.get(m, 0) + c1 * c2) % mod
    return out


# word-level integer polynomials: {sorted tuple of variables (with repetition): coeff}
def wp_add(p, q, k=1):
    out = dict(p)
    for m, c in q.items():
        v = out.get(m, 0) + k * c
        if v:
            out[m] = v
        else:
            out.pop(m, None)
    return out


def wp_mul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            v = out.get(m, 0) + c1 * c2
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    return out


def wp_subst(p, var, q):
    out = {}
    for m, c in p.items():
        k = m.count(var)
        rest = tuple(x for x in m if x != var)
        term = {rest: c}
        for _ in range(k):
            term = wp_mul(term, q)
        out = wp_add(out, term)
    return out


def wp_vars(p):
    return {v for m in p for v in m}


def merge_slices(p, values, lengths):
    """Use  W[a:c] = W[a:b] + 2^(b-a) W[b:c]  to coarsen, then replace whole computed words by their value."""
    changed = True
    while changed:
        changed = False
        vs = sorted(wp_vars(p))
        for u in vs:
            for v in vs:
                if u[0] == v[0] and u[2] == v[1]:
                    big = (u[0], u[1], v[2])
                    trial = wp_subst(p, u, {(big,): 1, (v,): -(1 << (u[2] - u[1]))})
                    if v not in wp_vars(trial):
                        p, changed = trial, True
                        break
            if changed:
                break
        if not changed:
            for u in vs:
                if u[0] in values and u[1] == 0 and u[2] >= lengths[u[0]]:
                    p, changed = wp_subst(p, u, values[u[0]]), True
                    break
    return p


def bounds(p):
    lo = hi = 0
    for m, c in p.items():
        top = c
        for v in m:
            top *= (1 << (v[2] - v[1])) - 1
        if c > 0:
            hi += top
        else:
            lo += top
    return lo, hi


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-mul.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        n, square = cert["n"], bool(cert["square"])
        inputs, outputs, tables = parse_blif(raw)
        want_in = ["a[%d]" % i for i in range(n)] + ([] if square else ["b[%d]" % i for i in range(n)])
        oname = "asquared" if square else "f"
        want_out = ["%s[%d]" % (oname, c) for c in range(2 * n)]
        if inputs != want_in or outputs != want_out:
            return {"ok": False, "reason": "interface"}
        polys = {o: lut_poly(ins, onset) for o, (ins, onset) in tables.items()}
        words = {"A": ["a[%d]" % i for i in range(n)]}
        if not square:
            words["B"] = ["b[%d]" % i for i in range(n)]
        values, lengths, used, last = {}, {}, set(), None
        for blk in cert["blocks"]:
            bid, width, out = blk["id"], blk["width"], blk["out"]
            if bid in words or type(width) is not int or width < 1 or len(out) != width:
                return {"ok": False, "reason": "block shape " + str(bid)}
            mod = 1 << width
            ops, syms = [], []
            for op in blk["operands"]:
                src, lo, hi = op["word"], op["lo"], op["hi"]
                if src not in words or not (0 <= lo < hi <= len(words[src])):
                    return {"ok": False, "reason": "operand of " + bid}
                ops.append(words[src][lo:hi])
                syms.append({((src, lo, hi),): 1})
            r = BitPoly(mod)
            limit = 64 * (len(blk["luts"]) + width * width + 64)
            for c, a in enumerate(out):
                for mono, k in atom_poly(a).items():
                    r.add(mono, k << c)
            for name in reversed(blk["luts"]):
                if name not in polys or name in used:
                    return {"ok": False, "reason": "LUT list of " + bid}
                used.add(name)
                r.substitute(name, polys[name])
                if len(r.terms) > limit:
                    return {"ok": False, "reason": "block %s: polynomial does not close" % bid}
            expect, value = {}, {}
            for coeff, idx in blk["expr"]:
                if type(coeff) is not int or not idx or len(idx) > 2 or any(not (0 <= i < len(ops)) for i in idx):
                    return {"ok": False, "reason": "expression of " + bid}
                t, v = {frozenset(): 1}, {(): 1}
                for i in idx:
                    t = bit_mul(t, word_bits(ops[i]), mod)
                    v = wp_mul(v, syms[i])
                for mono, k in t.items():
                    expect[mono] = (expect.get(mono, 0) + coeff * k) % mod
                value = wp_add(value, v, coeff)
            expect = {m: k for m, k in expect.items() if k}
            if r.terms != expect:
                return {"ok": False, "reason": "block %s: netlist polynomial differs from the declared expression" % bid}
            value = merge_slices(value, values, lengths)
            lo, hi = bounds(value)
            if lo < 0 or hi >= mod:
                return {"ok": False, "reason": "block %s: value range [%d, %d] outside the word" % (bid, lo, hi)}
            words[bid], values[bid] = out, value
            eff = width
            while eff and out[eff - 1] is None:
                eff -= 1
            lengths[bid] = eff
            last = bid
        if used != set(tables):
            return {"ok": False, "reason": "netlist has logic outside the derivation"}
        if words[last] != want_out:
            return {"ok": False, "reason": "last block is not the output vector"}
        a = ("A", 0, n)
        b = a if square else ("B", 0, n)
        if values[last] != {tuple(sorted((a, b))): 1}:
            return {"ok": False, "reason": "final value is not the product"}
        lev = {w: 0 for w in inputs}
        for o, (ins, _) in tables.items():          # file order is checked to be topological
            if any(v not in lev for v in ins):
                return {"ok": False, "reason": "netlist order"}
            lev[o] = 1 + max([lev[v] for v in ins] + [0])
        if len(tables) != cert["lut_count"] or max(lev.values()) != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "n": n, "square": square, "lut_count": len(tables), "levels": max(lev.values()),
                "blocks": len(cert["blocks"]), "netlist_digest": cert["netlist_digest"],
                "proof": "per-block polynomial identity mod 2^width from the netlist + integer range of each word"}
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
