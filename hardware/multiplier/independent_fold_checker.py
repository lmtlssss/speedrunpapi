"""Independent proof replay for colony.lut-div-fold.v1.  Shares no code with the compiler.

Claim: for all a, b:  b != 0 -> quotient = floor(a / b), remainder = a mod b;  b = 0 -> quotient = 2^n - 1, remainder = a.

The derivation names LUT groups and the wires of each word.  Everything else is recomputed here.
Parameters: g = fold + 2, t = m = g + 2, k = ceil(n / fold), P = n - 1 + m.

 1. digits    ABC cec against a counter of leading zeros:  s = lzc(b) for b != 0.
 2. triples   3b and 3a: ripple-adder cec.
 3. shifts    every LUT is a 4:1 select of the wires s positions down:  dn = b 2^s, dn3 = 3 dn, x = a 2^s, x3 = 3 x.
              (dn has its top bit set and nothing is shifted out, because s = lzc(b).)
 4. table     all 2^(t-1) readings of the top bits of dn are evaluated:  M3 = 3 M  and  0 <= 2^P - M dn < 2^(P-g)
              for every dn with those top bits.
 5. eps       heap polynomial + adder cec:  eps = -M dn mod 2^(P-g) = 2^P - M dn,  eps3 = 3 eps.
 6. X         heap polynomial, exact (guard columns, both sides below the modulus):  S + C = M x.
 7. folds     heap polynomial, exact:  S' + C' = low(S) + low(C) + (top(S) + top(C)) eps 2^(p-P).
              With W = S + C < 3 2^(p+fold), the tops are below 3 2^fold, so the columns above the field are zero and
              W' = W - T (2^P - eps) 2^(p-P) < 3 2^p.  The bound is evaluated here for the given parameters.
 8. R         heap polynomial mod 2^(n+2):  R = a - Q b + (constants that sum to zero),  Q = sum of the fields.
 9. final     M a 2^s = Q M dn + W with 0 <= W < 3 M dn, so 0 <= a - Q b < 3 b < 2^(n+2) and R is that value.
              R - b, R - 2b, Q + 1, Q + 2: heap polynomial + adder cec.  The output LUTs select by the two signs.
Lean (FoldDivision.lean) proves the step, the bound and the selection for all integers.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

from independent_mul_checker import parse_blif, lut_poly, BitPoly, bit_mul


class Bad(Exception):
    pass


def need(cond, why):
    if not cond:
        raise Bad(why)


def apoly(a):
    if a == 0:
        return {}
    if a == 1:
        return {frozenset(): 1}
    need(isinstance(a, str), "atom")
    if a.startswith("!"):
        return {frozenset(): 1, frozenset([a[1:]]): -1}
    return {frozenset([a]): 1}


def wire(a):
    return None if a in (0, 1) else a.lstrip("!")


def padd(p, q, k, mod):
    for mono, c in q.items():
        v = (p.get(mono, 0) + k * c) % mod
        if v:
            p[mono] = v
        else:
            p.pop(mono, None)


def word_poly(atoms, shift, mod):
    out = {}
    for i, a in enumerate(atoms):
        padd(out, apoly(a), 1 << (i + shift), mod)
    return out


def rows_poly(T, X, X3, shift, mod):
    """sum over radix-4 digits (t0, t1) of T:  4^j 2^shift [ t0(1-t1) X + t1(1-t0) 2X + t0 t1 X3 ]."""
    out = {}
    xp, x3p = word_poly(X, 0, mod), word_poly(X3, 0, mod)
    for j in range(0, len(T), 2):
        t0 = apoly(T[j])
        t1 = apoly(T[j + 1]) if j + 1 < len(T) else {}
        both = bit_mul(t0, t1, mod)
        s1, s2 = dict(t0), dict(t1)
        padd(s1, both, -1, mod)
        padd(s2, both, -1, mod)
        padd(out, bit_mul(s1, xp, mod), 1 << (shift + j), mod)
        padd(out, bit_mul(s2, xp, mod), 1 << (shift + j + 1), mod)
        padd(out, bit_mul(both, x3p, mod), 1 << (shift + j), mod)
    return out


def rows_of(rows, mod):
    out = {}
    for c, atoms in enumerate(rows):
        for a in atoms:
            padd(out, apoly(a), 1 << c, mod)
    return out


class Checker:
    def __init__(self, raw, cert, abc):
        self.cert, self.abc = cert, abc
        self.inputs, self.outputs, self.tables = parse_blif(raw)
        self.all = dict(self.tables)
        for name, (ins, rows) in cert["ghost"].items():
            need(name not in self.all and name not in self.inputs, "definition collides with the netlist: " + name)
            need(len(ins) <= 6 and all(len(r) == len(ins) and not set(r) - {"0", "1"} for r in rows), "definition " + name)
            self.all[name] = (list(ins), set(rows))
        self.used = set()
        self.tmp = tempfile.mkdtemp(prefix="foldchk_")
        self.calls = 0

    def claim(self, names):
        for o in names:
            need(o in self.all and o not in self.used, "LUT list: " + str(o))
            self.used.add(o)
        return list(names)

    # heap: rows (after replacing the block's LUTs by their polynomials) == expected, mod 2^width
    def heap(self, blk, expected, mod, label, upto_const=False):
        luts = self.claim(blk["luts"])
        r = BitPoly(mod)
        for c, atoms in enumerate(blk["rows"]):
            need(len(atoms) <= 2, label + ": more than two rows")
            for a in atoms:
                for mono, k in apoly(a).items():
                    r.add(mono, k << c)
        limit = 400 * (len(luts) + len(blk["rows"]) + 64)
        for name in reversed(luts):
            r.substitute(name, lut_poly(*self.all[name]))
            need(len(r.terms) <= limit, label + ": polynomial does not close")
        diff = dict(r.terms)
        padd(diff, expected, -1, mod)
        if upto_const:
            need(set(diff) <= {frozenset()}, label + ": rows differ from the declared sum")
            return diff.get(frozenset(), 0)
        need(not diff, label + ": rows differ from the declared sum")
        return 0

    def row_max(self, rows):
        return sum(len(atoms) << c for c, atoms in enumerate(rows))

    def run_cec(self, ins, outs, ours, ref, label):
        safe = lambda v: re.sub(r"[\[\]]", "_", v)
        self.calls += 1
        base = os.path.join(self.tmp, "c%d" % self.calls)
        for path, luts in ((base + "a.blif", ours), (base + "b.blif", ref)):
            L = [".model m", ".inputs " + " ".join(safe(v) for v in ins), ".outputs " + " ".join(outs)]
            for o, vs, rows in luts:
                if not rows:
                    L.append(".names " + safe(o))
                    continue
                L.append(".names " + " ".join([safe(v) for v in vs] + [safe(o)]))
                L += [r + " 1" if vs else "1" for r in rows]
            L.append(".end")
            open(path, "w").write("\n".join(L) + "\n")
        p = subprocess.run([self.abc, "-c", "cec -n %sa.blif %sb.blif" % (base, base)], capture_output=True, text=True, timeout=3000)
        need("Networks are equivalent" in p.stdout, label + ": not proved by cec")

    def atom_out(self, name, a):
        """A LUT that drives `name` with the value of atom a."""
        if a == 0:
            return (name, [], [])
        if a == 1:
            return (name, [], [""])
        return (name, [wire(a)], ["0" if a.startswith("!") else "1"])

    def free_inputs(self, luts, leaves, label):
        inside = set(luts)
        for o in luts:
            for v in self.all[o][0]:
                need(v in inside or v in leaves, label + ": reads a wire outside the block: " + v)

    # adder: out == sum of two rows mod 2^width, by cec against a ripple adder over the row wires
    def adder(self, blk, rows, width, label):
        luts = self.claim(blk["luts"])
        out = blk["out"]
        need(len(out) == width and len(rows) == width, label + ": width")
        leaves = []
        for atoms in rows:
            for a in atoms:
                if wire(a) and wire(a) not in leaves:
                    leaves.append(wire(a))
        self.free_inputs(luts, set(leaves), label)
        ours = [(o, self.all[o][0], sorted(self.all[o][1])) for o in luts]
        ours += [self.atom_out("o%d" % c, a) for c, a in enumerate(out)]
        ref, carry = [], None
        for c, atoms in enumerate(rows):
            vs = []
            for a in atoms:
                if wire(a) and wire(a) not in vs:
                    vs.append(wire(a))
            allv = vs + ([carry] if carry else [])
            srows, crows = [], []
            for bits in range(1 << len(allv)):
                env = {v: (bits >> q) & 1 for q, v in enumerate(allv)}
                tot = env[carry] if carry else 0
                for a in atoms:
                    tot += a if a in (0, 1) else (1 - env[a[1:]] if a.startswith("!") else env[a])
                key = "".join("1" if env[v] else "0" for v in allv)
                if tot & 1:
                    srows.append(key)
                if tot >> 1:
                    crows.append(key)
            ref.append(("o%d" % c, allv, srows))
            ref.append(("rc%d" % c, allv, crows))
            carry = "rc%d" % c
        self.run_cec(leaves, ["o%d" % c for c in range(width)], ours, ref, label)
        return out

    def sum_block(self, blk, expected, width, label):
        self.heap(blk["heap"], expected, 1 << width, label + " heap")
        return self.adder(blk, blk["heap"]["rows"], width, label + " adder")

    # value of atoms as functions of a few leaf wires, through the block's LUTs
    def fn(self, atoms, leaves, luts, label):
        nl = len(leaves)
        full = (1 << (1 << nl)) - 1
        env = {}
        for i, v in enumerate(leaves):
            env[v] = sum(1 << r for r in range(1 << nl) if (r >> i) & 1)
        inside = set(luts)

        def val(w):
            if w not in env:
                need(w in inside, label + ": reads a wire outside the block: " + w)
                ins, rows = self.all[w]
                acc = 0
                for row in rows:
                    tcube = full
                    for v, ch in zip(ins, row):
                        tcube &= val(v) if ch == "1" else ~val(v) & full
                    acc |= tcube
                env[w] = acc
            return env[w]
        out = []
        for a in atoms:
            out.append(0 if a == 0 else full if a == 1 else (~val(a[1:]) & full if a.startswith("!") else val(a)))
        return out, full

    def shift(self, blk, src, digs, width, label):
        luts = self.claim(blk["luts"])
        need(len(blk["stages"]) == len(digs), label + ": stages")
        word = list(src)
        j = len(digs)
        for tix, (stage, dg) in enumerate(zip(blk["stages"], digs)):
            need(len(stage) == width, label + ": width")
            step = 4 ** (j - 1 - tix)
            for c in range(width):
                srcs = [word[c - q * step] if 0 <= c - q * step < len(word) else 0 for q in range(4)]
                leaves = []
                for a in srcs + list(dg):
                    if wire(a) and wire(a) not in leaves:
                        leaves.append(wire(a))
                need(len(leaves) <= 6, label + ": leaves")
                vals, full = self.fn(srcs + list(dg) + [stage[c]], leaves, luts, label)
                s0, s1, s2, s3, d0, d1, got = vals
                want = (s0 & ~d0 & ~d1) | (s1 & d0 & ~d1) | (s2 & ~d0 & d1) | (s3 & d0 & d1)
                need(got == want & full, "%s: stage %d bit %d is not the select" % (label, tix, c))
            word = stage
        return word

    def run(self):
        cert = self.cert
        n, b = cert["n"], cert["b"]
        need(type(n) is int and type(b) is int and b >= 1, "parameters")
        g = b + 2
        t = m = g + 2
        k = -(-n // b)
        P, npad, fw, wr, we = n - 1 + m, k * b, b + 2, n + 2, n - 1 + m - g
        need(n >= t, "width below the table index")
        A = ["a[%d]" % i for i in range(n)]
        Bw = ["b[%d]" % i for i in range(n)]
        need(self.inputs == A + Bw, "inputs")
        need(self.outputs == ["quotient[%d]" % i for i in range(n)] + ["remainder[%d]" % i for i in range(n)], "outputs")
        # 1 digits
        j = 1
        while 4 ** j < n:
            j += 1
        dg = cert["digits"]
        luts = self.claim(dg["luts"])
        digs = dg["out"]
        need(len(digs) == j and all(len(q) == 2 for q in digs), "digits")
        self.free_inputs(luts, set(Bw), "digits")
        ours = [(o, self.all[o][0], sorted(self.all[o][1])) for o in luts]
        names = []
        for tix, pair in enumerate(digs):
            for h in (0, 1):
                bit = 2 * (j - 1 - tix) + h
                ours.append(self.atom_out("s%d" % bit, pair[h]))
                names.append("s%d" % bit)
        wd = 4 ** j
        ref, seen = [], None
        therm = {}
        for q in range(1, wd):                                # therm[q] = 1 iff the top q bits are all zero
            src = wd - q - (wd - n)                             # bit of b at padded position wd - q
            bitw = Bw[src] if 0 <= src < n else None
            name = "z%d" % q
            if seen is None:
                ref.append((name, [bitw], ["0"]) if bitw else (name, [], [""]))
            elif bitw:
                ref.append((name, [seen, bitw], ["10"]))
            else:
                ref.append((name, [seen], ["1"]))
            seen = name
            therm[q] = name
        for bit in range(2 * j):
            acc = None
            for q in range(1 << bit, wd, 1 << bit):
                nm = "x%d_%d" % (bit, q)
                ref.append((nm, [acc, therm[q]], ["10", "01"]) if acc else (nm, [therm[q]], ["1"]))
                acc = nm
            ref.append(("s%d" % bit, [acc], ["1"]))
        self.run_cec(Bw, names, ours, ref, "digits")
        # 2 triples
        def triple(blk, word, label):
            rows = [[] for _ in range(len(word) + 2)]
            for c, a in enumerate(word):
                rows[c].append(a)
                rows[c + 1].append(a)
            width = len(word) + 2
            exp = rows_of(rows, 1 << width)
            return self.sum_block(blk, exp, width, label)
        d3 = triple(cert["d3"], Bw, "3b")
        a3 = triple(cert["a3"], A, "3a")
        # 3 shifts
        dn = self.shift(cert["dn"], Bw, digs, n, "dn")
        dn3 = self.shift(cert["dn3"], d3, digs, n + 2, "dn3")
        x = self.shift(cert["x"], A, digs, 2 * n - 1, "x")
        x3 = self.shift(cert["x3"], a3, digs, 2 * n + 1, "x3")
        # 4 table
        tb = cert["table"]
        luts = self.claim(tb["luts"])
        Mw, M3 = tb["M"], tb["M3"]
        need(len(Mw) == m and len(M3) == m + 2, "table widths")
        ix = dn[n - t:n - 1]
        leaves = [wire(a) for a in ix]
        need(all(leaves) and len(set(leaves)) == len(leaves) and not any(a.startswith("!") for a in ix), "table index wires")
        vals, full = self.fn(Mw + M3, leaves, luts, "table")
        for r in range(1 << (t - 1)):
            mv = sum(((vals[q] >> r) & 1) << q for q in range(m))
            m3v = sum(((vals[m + q] >> r) & 1) << q for q in range(m + 2))
            lo = ((1 << (t - 1)) | r) << (n - t)
            hi = lo + (1 << (n - t)) - 1
            need(m3v == 3 * mv, "table: M3 is not 3 M")
            need((1 << P) - mv * hi >= 0 and (1 << P) - mv * lo < 1 << (P - g), "table: M dn outside (2^P - 2^(P-g), 2^P]")
        # 5 eps
        mod = 1 << we
        exp = {}
        padd(exp, rows_poly(Mw, dn, dn3, 0, mod), -1, mod)
        eps = self.sum_block(cert["eps"], exp, we, "eps")
        mod = 1 << (we + 2)
        exp = {}
        padd(exp, rows_poly(M3, dn, dn3, 0, mod), -1, mod)
        eps3 = self.sum_block(cert["eps3"], exp, we + 2, "eps3")
        # 6 X
        gw = cert["X"]["width"]
        need(gw >= P + n and len(cert["X"]["rows"]) == gw, "X width")
        mod = 1 << gw
        self.heap(cert["X"], rows_poly(Mw, x, x3, 0, mod), mod, "X")
        need(self.row_max(cert["X"]["rows"]) < mod and (1 << (m + 2 * n + 1)) <= mod, "X: not exact")
        rows = cert["X"]["rows"]
        bound = 1 << (P + n)                                   # X = M x < 2^P 2^n, since M dn <= 2^P and x < 2^n dn
        # 7 folds, 8 R
        need(len(cert["folds"]) == k - 1 and len(cert["R"]) == k, "fold count")
        rmod = 1 << wr
        rprev = [[a] for a in A] + [[], []]
        ksum = 0
        fields = []
        for i in range(k):
            p = P + npad - (i + 1) * b
            off = p - P
            need(bound <= 3 << (p + b), "bound before fold %d" % i)
            TS, TC = [0] * fw, [0] * fw
            for c in range(p, min(p + fw, len(rows))):
                atoms = rows[c]
                if atoms:
                    TS[c - p] = atoms[0]
                if len(atoms) > 1:
                    TC[c - p] = atoms[1]
            fields.append((off, TS, TC))
            exp = rows_of(rprev, rmod)
            padd(exp, rows_poly(TS, Bw, d3, off, rmod), -1, rmod)
            padd(exp, rows_poly(TC, Bw, d3, off, rmod), -1, rmod)
            blk = cert["R"][i]
            need(blk["width"] == wr and len(blk["rows"]) == wr, "R width")
            ksum += self.heap(blk, exp, rmod, "R %d" % i, upto_const=True)
            rprev = blk["rows"]
            if i == k - 1:
                break
            blk = cert["folds"][i]
            gw = blk["width"]
            need(gw >= p + 2 and len(blk["rows"]) == gw, "fold width")
            mod = 1 << gw
            exp = rows_of(rows[:p], mod)
            padd(exp, rows_poly(TS, eps, eps3, off, mod), 1, mod)
            padd(exp, rows_poly(TC, eps, eps3, off, mod), 1, mod)
            self.heap(blk, exp, mod, "fold %d" % i)
            tmax = (3 << b) - 1                                 # each top field, and their sum, is at most W / 2^p
            wmax = 2 * ((1 << p) - 1) + tmax * ((1 << (P - g)) - 1) * (1 << off)
            need(self.row_max(blk["rows"]) < mod and 2 * ((1 << p) - 1) + 2 * ((1 << fw) - 1) * 3 * (1 << we) * (1 << off) < mod, "fold %d: not exact" % i)
            need(wmax < 3 << p and (3 << b) <= 1 << fw, "fold %d: bound" % i)
            bound = 3 << p
            rows = blk["rows"]
        need(ksum % rmod == 0, "R constants do not cancel")
        # last field: W = T 2^P + L, L < 2 2^P;  M x - Q M dn = L + T eps < 3 (2^P - 2^(P-g)) <= 3 M dn
        need(2 * ((1 << P) - 1) + ((3 << b) - 1) * ((1 << (P - g)) - 1) < 3 * ((1 << P) - (1 << (P - g)) + 1), "final bound")
        need(3 * ((1 << n) - 1) < rmod, "R width")
        # 9 final
        fin = cert["final"]
        rp = rows_of(rprev, rmod)
        R0 = self.sum_block(fin["R0"], rp, wr, "R")
        dpoly = word_poly(Bw, 0, rmod)
        e1 = dict(rp)
        padd(e1, dpoly, -1, rmod)
        R1 = self.sum_block(fin["R1"], e1, wr, "R - b")
        e2 = dict(rp)
        padd(e2, dpoly, -2, rmod)
        R2 = self.sum_block(fin["R2"], e2, wr, "R - 2b")
        qmod = 1 << n
        qp = {}
        for off, TS, TC in fields:
            padd(qp, word_poly(TS, off, qmod), 1, qmod)
            padd(qp, word_poly(TC, off, qmod), 1, qmod)
        need(len(fin["Q"]) == 3, "Q")
        Q = []
        for add in range(3):
            e = dict(qp)
            padd(e, {frozenset(): 1}, add, qmod)
            Q.append(self.sum_block(fin["Q"][add], e, n, "Q + %d" % add))
        nz = fin["nz"]
        luts = self.claim(nz["luts"])
        self.free_inputs(luts, set(Bw), "nonzero")
        ours = [(o, self.all[o][0], sorted(self.all[o][1])) for o in luts] + [self.atom_out("nz", nz["out"])]
        ref, acc = [], None
        for i, w in enumerate(Bw):
            ref.append(("or%d" % i, [acc, w], ["10", "11", "01"]) if acc else ("or%d" % i, [w], ["1"]))
            acc = "or%d" % i
        ref.append(("nz", [acc], ["1"]))
        self.run_cec(Bw, ["nz"], ours, ref, "nonzero")
        sel = self.claim(fin["select"]["luts"])
        n1, n2 = R1[wr - 1], R2[wr - 1]
        for c in range(n):
            for kind, srcs in (("remainder", [R0[c], R1[c], R2[c], n1, n2]), ("quotient", [Q[0][c], Q[1][c], Q[2][c], n1, n2, nz["out"]])):
                leaves = []
                for a in srcs:
                    if wire(a) and wire(a) not in leaves:
                        leaves.append(wire(a))
                vals, full = self.fn(srcs + ["%s[%d]" % (kind, c)], leaves, sel, kind)
                v0, v1, v2, s1, s2 = vals[:5]
                want = (v2 & ~s2) | (v1 & s2 & ~s1) | (v0 & s2 & s1)
                if kind == "quotient":
                    want = (want & vals[5]) | (~vals[5] & full)
                need(vals[-1] == want & full, "%s[%d] is not the selection" % (kind, c))
        need(self.used == set(self.all), "logic outside the derivation")
        lev = {v: 0 for v in self.inputs}
        for o, (vs, _) in self.tables.items():
            need(all(v in lev for v in vs), "netlist order")
            lev[o] = 1 + max([lev[v] for v in vs] + [0])
        need(len(self.tables) == cert["lut_count"] and max(lev.values()) == cert["levels"], "declared cost differs")
        return {"ok": True, "n": n, "fold": b, "lut_count": len(self.tables), "levels": max(lev.values()), "cec_calls": self.calls,
                "netlist_digest": cert["netlist_digest"],
                "proof": "heap polynomial identities from the netlist, table by enumeration, adders and leading-zero count by ABC cec, bounds evaluated"}


def verify(raw, cert, abc="yosys-abc"):
    try:
        if cert.get("schema") != "colony.lut-div-fold.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        return Checker(raw, cert, abc).run()
    except Bad as exc:
        return {"ok": False, "reason": str(exc)}
    except Exception as exc:
        return {"ok": False, "reason": "replay exception: " + type(exc).__name__ + ": " + str(exc)[:200]}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--netlist", type=Path, required=True)
    ap.add_argument("--derivation", type=Path, required=True)
    ap.add_argument("--abc", default="yosys-abc")
    args = ap.parse_args()
    res = verify(args.netlist.read_bytes(), json.loads(args.derivation.read_text()), args.abc)
    print(json.dumps(res, sort_keys=True))
    raise SystemExit(0 if res["ok"] else 1)
