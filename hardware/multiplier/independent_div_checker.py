"""Independent proof replay for colony.lut-div.v1.

Claim: quotient = floor(a / b) and remainder = a mod b for every n-bit a and b > 0;
       quotient = 2^n - 1 and remainder = a for b = 0.

Recurrence.  A_j = top j bits of a, s = [r < 0], r_0 = 0:
    r_j = 2 r_{j-1} + a_bit + (b xnor s) + (1 - s)        (mod 2^(j+1))
    s_j = [b >= 2^j] or top bit of r_j,        q_j = not s_j
Without the modulus this is non-restoring division: r_j = 2 r_{j-1} + a_bit - b for s = 0 and + b for
s = 1, with -b <= r_j < b, and r_j >= 0 exactly when the j-th quotient bit is 1.  If b >= 2^j then
b > A_j, the quotient prefix is 0 and r_j < 0.  If b < 2^j then |r_j| < 2^j, so j+1 bits hold r_j and
its top bit is the sign.  The kept word is always r_j mod 2^(j+1), which is all the next row reads.
GrowingWordDivision.lean proves this for every width in Lean 4 (theorems div_correct, div_zero).
remainder = r_n + (s_n ? b : 0)  (mod 2^n).  For b = 0 no row goes negative.

This program checks that the netlist is that recurrence: per row, the polynomial of the row's outputs
rebuilt from the netlist equals the right-hand side; each quotient LUT is the stated NOR and the bits it
reads cover b_j .. b_(n-1); the remainder row equals its expression.
"""
import argparse
import hashlib
import json
from pathlib import Path

from independent_mul_checker import parse_blif, lut_poly, atom_poly, BitPoly
from independent_sqrt_checker import pmul, padd, xnor_poly, aeval, avars


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-div.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        n = cert["n"]
        inputs, outputs, tables = parse_blif(raw)
        if inputs != ["a[%d]" % i for i in range(n)] + ["b[%d]" % i for i in range(n)] or \
                outputs != ["quotient[%d]" % i for i in range(n)] + ["remainder[%d]" % i for i in range(n)]:
            return {"ok": False, "reason": "interface"}
        polys = {o: lut_poly(ins, onset) for o, (ins, onset) in tables.items()}
        used = set()
        covers = {"b[%d]" % i: {i} for i in range(n)}          # wire -> the bits of b it is the OR of

        def take(name):
            if name in used or name not in tables:
                raise ValueError("LUT list: " + str(name))
            used.add(name)

        for fl in cert["flags"]:
            name = fl["lut"]
            take(name)
            ins, onset = tables[name]
            if any(v not in covers for v in ins) or len(onset) != (1 << len(ins)) - 1 or "0" * len(ins) in onset:
                return {"ok": False, "reason": "flag " + name}
            covers[name] = set().union(*[covers[v] for v in ins])
            if covers[name] != set(range(fl["i"], n)):
                return {"ok": False, "reason": "flag range " + name}
        if len(cert["rows"]) != n:
            return {"ok": False, "reason": "rows"}
        r, s = [], None
        for j in range(1, n + 1):
            row = cert["rows"][j - 1]
            w, mod = j + 1, 1 << (j + 1)
            out = row["out"]
            if len(out) != w:
                return {"ok": False, "reason": "row %d shape" % j}
            expect = {}
            padd(expect, atom_poly("a[%d]" % (n - j)), 1, mod)
            for c in range(1, w):
                if c - 1 < len(r):
                    padd(expect, atom_poly(r[c - 1]), 1 << c, mod)
            for c in range(w):
                padd(expect, xnor_poly("b[%d]" % c if c < n else None, s, mod), 1 << c, mod)
            padd(expect, {frozenset(): 1}, 1, mod)
            padd(expect, atom_poly(s), -1, mod)
            got = BitPoly(mod)
            for c, a in enumerate(out):
                for mono, kk in atom_poly(a).items():
                    got.add(mono, kk << c)
            for name in reversed(row["luts"]):
                take(name)
                got.substitute(name, polys[name])
                if len(got.terms) > 4096 * w:
                    return {"ok": False, "reason": "row %d: polynomial does not close" % j}
            if got.terms != expect:
                return {"ok": False, "reason": "row %d is not the recurrence" % j}
            qname = "quotient[%d]" % (n - j)
            take(qname)
            ins, onset = tables[qname]
            top = out[w - 1]
            tv = avars(top)
            rest = [v for v in ins if v not in tv]
            if any(v not in covers for v in rest) or set(tv) - set(ins):
                return {"ok": False, "reason": "row %d: quotient inputs" % j}
            cov = set().union(*[covers[v] for v in rest]) if rest else set()
            if cov != set(range(j, n)):
                return {"ok": False, "reason": "row %d: quotient LUT does not read b >= 2^j" % j}
            for bits in range(1 << len(ins)):
                env = {v: (bits >> t) & 1 for t, v in enumerate(ins)}
                want = not (aeval(top, env) or any(env[v] for v in rest))
                key = "".join("1" if env[v] else "0" for v in ins)
                if (key in onset) != want:
                    return {"ok": False, "reason": "row %d: quotient table" % j}
            r, s = out, "!" + qname
        mod = 1 << n
        expect = {}
        for c in range(n):
            padd(expect, atom_poly(r[c]), 1 << c, mod)
            padd(expect, pmul(atom_poly("b[%d]" % c), atom_poly(s), mod), 1 << c, mod)
        got = BitPoly(mod)
        for c in range(n):
            got.add(frozenset(["remainder[%d]" % c]), 1 << c)
        for name in reversed(cert["rem"]):
            take(name)
            got.substitute(name, polys[name])
            if len(got.terms) > 4096 * n:
                return {"ok": False, "reason": "remainder: polynomial does not close"}
        if got.terms != expect:
            return {"ok": False, "reason": "remainder row is not r + s*b"}
        if used != set(tables):
            return {"ok": False, "reason": "netlist has logic outside the derivation"}
        lev = {v: 0 for v in inputs}
        for o, (ins, _) in tables.items():
            if any(v not in lev for v in ins):
                return {"ok": False, "reason": "netlist order"}
            lev[o] = 1 + max([lev[v] for v in ins] + [0])
        if len(tables) != cert["lut_count"] or max(lev.values()) != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "n": n, "lut_count": len(tables), "levels": max(lev.values()),
                "netlist_digest": cert["netlist_digest"],
                "proof": "each row equals the non-restoring recurrence (polynomial identity mod 2^(j+1)); recurrence lemma in the header"}
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
