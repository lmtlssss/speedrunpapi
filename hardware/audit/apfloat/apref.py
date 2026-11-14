#!/usr/bin/env python3
"""Exact reference for llvm::APFloat on its small formats, and the comparison with the harness.

usage: apref.py APF OUTDIR FORMATS KINDS [JOBS]

APF      the harness binary (apf, apf_trunk)
OUTDIR   one .bad file per run that has a wrong result, one .json per run, summary.tsv
FORMATS  comma-separated: E5M2,E5M2FNUZ,E4M3,E4M3FN,E4M3FNUZ,E4M3B11FNUZ,E3M4,E8M0FNU,E3M2FN,E2M3FN,E2M1FN
KINDS    comma-separated: bin (add sub mul div, five modes), remmod, rint, next, cmp, conv, toint, fromint, fma

The value set of a format is read from the library itself (apf table): every bit pattern, its class and its
value. Everything else is computed here with integers: the exact result of the operation, rounded once to
the grid of precision p and least exponent emin, in the mode asked for. A result above the largest finite
number overflows by the IEEE 754 rule; where the format has no infinity and has a NaN the header says what
happens ("operations that would ordinarily produce Inf produce NaN instead"). Where the format has no way
to write the result and the header does not say what happens (a NaN or an infinity in the three formats
that have neither, a zero or a negative number in a format without them), the case is not judged: it is
counted under its own name with what the library returned.
"""
import collections
import json
import multiprocessing
import os
import subprocess
import sys

ZERO, FIN, INF, NAN = "z", "f", "i", "n"
MODES = ["ne", "tp", "tn", "tz", "na"]


def round_up(q, r, d, neg, mode):
    """1 when the magnitude q + r/d rounds up to q + 1."""
    if r == 0:
        return 0
    if mode == "ne":
        return 1 if (2 * r > d or (2 * r == d and (q & 1))) else 0
    if mode == "na":
        return 1 if 2 * r >= d else 0
    if mode == "tz":
        return 0
    if mode == "tp":
        return 0 if neg else 1
    return 1 if neg else 0


class Fmt:
    def __init__(self, apf, name):
        self.name = name
        w = subprocess.run([apf, "info", name], capture_output=True, text=True, check=True).stdout.split()
        self.bits, self.prec, self.emin, self.emax = int(w[1]), int(w[3]), int(w[5]), int(w[7])
        n = 1 << self.bits
        self.K = [None] * n
        self.NEG = [False] * n
        self.M = [0] * n
        self.E = [0] * n
        self.val = [None] * n
        self.find = {}
        self.pz = self.nz = self.pinf = self.ninf = None
        self.nans = set()
        table = subprocess.run([apf, "table", name], capture_output=True, text=True, check=True).stdout
        for line in table.splitlines():
            p, kind, sign, val = line.split()
            p = int(p, 16)
            neg = sign == "1"
            self.NEG[p] = neg
            if kind == "nan":
                self.K[p] = NAN
                self.nans.add(p)
            elif kind == "inf":
                self.K[p] = INF
                if neg:
                    self.ninf = p
                else:
                    self.pinf = p
            elif kind == "zero":
                self.K[p] = ZERO
                self.val[p] = 0.0
                if neg:
                    self.nz = p
                else:
                    self.pz = p
            else:
                self.K[p] = FIN
                f = float.fromhex(val)
                self.val[p] = f
                num, den = abs(f).as_integer_ratio()
                e = -(den.bit_length() - 1)
                while not num & 1:
                    num >>= 1
                    e += 1
                self.M[p] = num
                self.E[p] = e
                assert (neg, num, e) not in self.find, (name, p)
                assert neg == (f < 0), (name, p)
                self.find[(neg, num, e)] = p
        pos = [p for p in range(n) if self.K[p] == FIN and not self.NEG[p]]
        negs = [p for p in range(n) if self.K[p] == FIN and self.NEG[p]]
        self.pmax = max(pos, key=lambda p: self.val[p])
        self.pmin = min(pos, key=lambda p: self.val[p])
        self.nmax = min(negs, key=lambda p: self.val[p]) if negs else None
        # the finite values in order, zero once
        seen = {}
        for p in range(n):
            if self.K[p] in (FIN, ZERO):
                seen.setdefault(self.val[p], p)
        self.order = sorted(seen.items())
        self.rank = {v: i for i, (v, _) in enumerate(self.order)}

    # -- how the format writes a result -------------------------------------------------------------
    def r_zero(self, neg, fl):
        if neg and self.nz is not None:
            return ("P", self.nz, fl)
        if self.pz is not None:
            return ("P", self.pz, fl)
        return ("U", "zero", None)

    def r_inf(self, neg, tag, fl):
        if self.pinf is not None:
            return ("P", self.ninf if neg else self.pinf, fl)
        if self.nans:
            return ("N", None, fl)
        return ("U", tag, None)

    def r_nan(self, tag, fl):
        if self.nans:
            return ("N", None, fl)
        return ("U", tag, None)

    def above_max(self, m, t):
        M, E = self.M[self.pmax], self.E[self.pmax]
        c = min(t, E)
        return (m << (t - c)) > (M << (E - c))

    def exact(self, m, t, neg, fl, tag):
        """The value m * 2**t, m > 0, which the operation returns without rounding."""
        while not m & 1:
            m >>= 1
            t += 1
        p = self.find.get((neg, m, t))
        if p is not None:
            return ("P", p, fl)
        return ("U", tag, None)

    def rnd(self, num, den, x2, neg, mode):
        """num/den * 2**x2 > 0 with the sign neg, rounded once to the format."""
        e = num.bit_length() - den.bit_length()
        if e >= 0:
            if num < (den << e):
                e -= 1
        elif (num << -e) < den:
            e -= 1
        ex = e + x2
        t = (ex if ex > self.emin else self.emin) - self.prec + 1
        s = t - x2
        if s >= 0:
            d = den << s
            q, r = divmod(num, d)
        else:
            d = den
            q, r = divmod(num << -s, d)
        m = q + round_up(q, r, d, neg, mode)
        if r == 0:
            fl = (0, 0)
        elif ex < self.emin:
            # tiny before rounding; tiny after rounding unless the rounding to p digits reaches 2**emin
            after = 24
            if ex == self.emin - 1:
                s2 = (ex - self.prec + 1) - x2
                if s2 >= 0:
                    d2 = den << s2
                    q2, r2 = divmod(num, d2)
                else:
                    d2 = den
                    q2, r2 = divmod(num << -s2, d2)
                if q2 + round_up(q2, r2, d2, neg, mode) == (1 << self.prec):
                    after = 16
            fl = (after, 24)
        else:
            fl = (16, 16)
        if m == 0:
            return self.r_zero(neg, fl)
        while not m & 1:
            m >>= 1
            t += 1
        p = self.find.get((neg, m, t))
        if p is not None:
            return ("P", p, fl)
        if neg and self.nmax is None:
            return ("U", "negative", None)
        if not self.above_max(m, t):
            raise ValueError("no pattern for %s%d*2^%d in %s" % ("-" if neg else "", m, t, self.name))
        if mode in ("ne", "na") or (mode == "tp" and not neg) or (mode == "tn" and neg):
            return self.r_inf(neg, "overflow", (20, 20))
        return ("P", self.nmax if neg else self.pmax, (20, 20))


# -- the operations ---------------------------------------------------------------------------------

def x_addsub(F, mode, a, b, sub):
    K, NEG, M, E = F.K, F.NEG, F.M, F.E
    ka, kb = K[a], K[b]
    if ka == NAN or kb == NAN:
        return ("N", None, None)
    na, nb = NEG[a], NEG[b] != sub
    if ka == INF:
        if kb == INF and na != nb:
            return F.r_nan("invalid", (1, 1))
        return ("P", a, (0, 0))
    if kb == INF:
        return ("P", F.ninf if nb else F.pinf, (0, 0))
    if ka == ZERO and kb == ZERO:
        return F.r_zero(na if na == nb else mode == "tn", (0, 0))
    c = min(E[a], E[b])
    n = (-(M[a] << (E[a] - c)) if na else (M[a] << (E[a] - c))) + (-(M[b] << (E[b] - c)) if nb else (M[b] << (E[b] - c)))
    if n == 0:
        return F.r_zero(mode == "tn", (0, 0))
    return F.rnd(abs(n), 1, c, n < 0, mode)


def x_mul(F, mode, a, b):
    K, NEG, M, E = F.K, F.NEG, F.M, F.E
    ka, kb = K[a], K[b]
    if ka == NAN or kb == NAN:
        return ("N", None, None)
    neg = NEG[a] != NEG[b]
    if ka == INF or kb == INF:
        if ka == ZERO or kb == ZERO:
            return F.r_nan("invalid", (1, 1))
        return ("P", F.ninf if neg else F.pinf, (0, 0))
    if ka == ZERO or kb == ZERO:
        return F.r_zero(neg, (0, 0))
    return F.rnd(M[a] * M[b], 1, E[a] + E[b], neg, mode)


def x_div(F, mode, a, b):
    K, NEG, M, E = F.K, F.NEG, F.M, F.E
    ka, kb = K[a], K[b]
    if ka == NAN or kb == NAN:
        return ("N", None, None)
    neg = NEG[a] != NEG[b]
    if ka == INF:
        if kb == INF:
            return F.r_nan("invalid", (1, 1))
        return ("P", F.ninf if neg else F.pinf, (0, 0))
    if kb == INF:
        return F.r_zero(neg, (0, 0))
    if kb == ZERO:
        if ka == ZERO:
            return F.r_nan("invalid", (1, 1))
        return F.r_inf(neg, "divzero", (2, 2))
    if ka == ZERO:
        return F.r_zero(neg, (0, 0))
    return F.rnd(M[a], M[b], E[a] - E[b], neg, mode)


def x_remmod(F, op, a, b):
    K, NEG, M, E = F.K, F.NEG, F.M, F.E
    ka, kb = K[a], K[b]
    if ka == NAN or kb == NAN:
        return ("N", None, None)
    if ka == INF or kb == ZERO:
        return F.r_nan("invalid", (1, 1))
    if kb == INF or ka == ZERO:
        return ("P", a, (0, 0))
    c = min(E[a], E[b])
    x, y = M[a] << (E[a] - c), M[b] << (E[b] - c)
    q, r = divmod(x, y)
    neg = NEG[a]
    if op == "rem" and (2 * r > y or (2 * r == y and (q & 1))):
        r = y - r
        neg = not neg
    if r == 0:
        return F.r_zero(NEG[a], (0, 0))
    return F.exact(r, c, neg, (0, 0), "negative" if (neg and F.nmax is None) else "unrepresentable")


def x_rint(F, mode, a):
    k = F.K[a]
    if k == NAN:
        return ("N", None, None)
    if k in (INF, ZERO) or F.E[a] >= 0:
        return ("P", a, (0, 0))
    d = 1 << -F.E[a]
    q, r = divmod(F.M[a], d)
    n = q + round_up(q, r, d, F.NEG[a], mode)
    if n == 0:
        return F.r_zero(F.NEG[a], (16, 16))
    return F.exact(n, 0, F.NEG[a], (16, 16), "integer above the largest finite number")


def x_next(F, down, a):
    k = F.K[a]
    if k == NAN:
        return ("N", None, None)
    if k == INF:
        if F.NEG[a] == down:
            return ("P", a, (0, 0))
        return ("P", F.pmax if down else F.nmax, (0, 0))
    j = F.rank[F.val[a] if k == FIN else 0.0] + (-1 if down else 1)
    if j < 0:
        if F.nmax is None:
            return ("U", "below the least value", None)
        return F.r_inf(True, "below the least value", (0, 0))
    if j >= len(F.order):
        return F.r_inf(False, "above the largest value", (0, 0))
    v, p = F.order[j]
    if v == 0.0:
        return F.r_zero(not down, (0, 0))
    return ("P", p, (0, 0))


def x_conv(F, T, mode, a):
    k = F.K[a]
    if k == NAN:
        return T.r_nan("nan", None)
    if k == INF:
        return T.r_inf(F.NEG[a], "inf", None)
    if k == ZERO:
        return T.r_zero(F.NEG[a], None)
    return T.rnd(F.M[a], 1, F.E[a], F.NEG[a], mode)


def x_toint(F, width, signed, mode, a):
    """(integer as an unsigned pattern, status, isExact)"""
    lo, hi = (-(1 << (width - 1)), (1 << (width - 1)) - 1) if signed else (0, (1 << width) - 1)
    mask = (1 << width) - 1
    k, neg = F.K[a], F.NEG[a]
    if k == NAN:
        return (0, 1, 0)
    if k == INF:
        return ((lo if neg else hi) & mask, 1, 0)
    if k == ZERO:
        return (0, 0, 0 if neg else 1)
    if F.E[a] >= 0:
        n, r = F.M[a] << F.E[a], 0
    else:
        d = 1 << -F.E[a]
        q, r = divmod(F.M[a], d)
        n = q + round_up(q, r, d, neg, mode)
    v = -n if neg else n
    if v < lo:
        return (lo & mask, 1, 0)
    if v > hi:
        return (hi & mask, 1, 0)
    return (v & mask, 16 if r else 0, 0 if r else 1)


def x_fromint(F, width, signed, mode, n):
    v = n - (1 << width) if (signed and n >> (width - 1)) else n
    if v == 0:
        return F.r_zero(False, (0, 0))
    return F.rnd(abs(v), 1, 0, v < 0, mode)


def x_cmp(F, a, b):
    if F.K[a] == NAN or F.K[b] == NAN:
        return 3
    def key(p):
        if F.K[p] == INF:
            return (-1 if F.NEG[p] else 1, 0.0)
        return (0, F.val[p])
    x, y = key(a), key(b)
    return 0 if x < y else (1 if x == y else 2)


def x_scalbn(F, mode, a, n):
    k = F.K[a]
    if k == NAN:
        return ("N", None, None)
    if k in (INF, ZERO):
        return ("P", a, None)
    r = F.rnd(F.M[a], 1, F.E[a] + n, F.NEG[a], mode)
    return (r[0], r[1], None)


INT_MIN = -(1 << 31)


def x_misc(F, a):
    """(ilogb, getExactLog2Abs, isDenormal, isSmallest, isSmallestNormalized, isLargest, isNormal, inverse)"""
    k = F.K[a]
    if k == NAN:
        return (INT_MIN, INT_MIN, 0, 0, 0, 0, 0, "-")
    if k == INF:
        return ((1 << 31) - 1, INT_MIN, 0, 0, 0, 0, 0, "-")
    if k == ZERO:
        return (INT_MIN + 1, INT_MIN, 0, 0, 0, 0, 0, "-")
    m, e = F.M[a], F.E[a]
    lg = e + m.bit_length() - 1
    pow2 = m == 1
    den = lg < F.emin
    mag = abs(F.val[a])
    inv = "-"
    if pow2 and not den and -lg >= F.emin:
        p = F.find.get((F.NEG[a], 1, -lg))
        if p is not None:
            inv = "f %x" % p
    return (lg, lg if pow2 else INT_MIN, int(den), int(mag == F.val[F.pmin]), int(pow2 and lg == F.emin),
            int(mag == F.val[F.pmax]), int(not den), inv)


def x_fma(F, mode, a, b, c):
    K, NEG, M, E = F.K, F.NEG, F.M, F.E
    ka, kb, kc = K[a], K[b], K[c]
    if ka == NAN or kb == NAN or kc == NAN:
        return ("N", None, None)
    sab = NEG[a] != NEG[b]
    if ka == INF or kb == INF:
        if ka == ZERO or kb == ZERO:
            return F.r_nan("invalid", (1, 1))
        if kc == INF and NEG[c] != sab:
            return F.r_nan("invalid", (1, 1))
        return ("P", F.ninf if sab else F.pinf, (0, 0))
    if kc == INF:
        return ("P", c, (0, 0))
    if ka == ZERO or kb == ZERO:
        if kc == ZERO:
            return F.r_zero(sab if sab == NEG[c] else mode == "tn", (0, 0))
        return ("P", c, (0, 0))
    pm, pe = M[a] * M[b], E[a] + E[b]
    if kc == ZERO:
        return F.rnd(pm, 1, pe, sab, mode)
    x = min(pe, E[c])
    n = (-(pm << (pe - x)) if sab else (pm << (pe - x))) + (-(M[c] << (E[c] - x)) if NEG[c] else (M[c] << (E[c] - x)))
    if n == 0:
        return F.r_zero(mode == "tn", (0, 0))
    return F.rnd(abs(n), 1, x, n < 0, mode)


# -- one run ----------------------------------------------------------------------------------------

def describe(F, cat, bits):
    """What the library returned, in words, for the cases that are not judged."""
    if cat == "!":
        return "signal %s" % bits
    if cat.endswith("!"):
        return "class %s, then signal %s on reading its bits" % ({"n": "NaN", "i": "infinity"}.get(cat[0], cat[0]), bits)
    k = F.K[bits] if bits < len(F.K) else None
    if cat == "n":
        return "NaN" if k == NAN else "class NaN, pattern %x" % bits
    if cat == "i":
        return "infinity" if k == INF else "class infinity, pattern %x" % bits
    if cat == "z":
        return ("-0" if F.NEG[bits] else "+0") if k == ZERO else "class zero, pattern %x" % bits
    if bits == F.pmax:
        return "largest finite"
    if bits == F.nmax:
        return "-largest finite"
    if bits == F.pmin:
        return "least positive"
    return "another finite value"


def run(job):
    apf, outdir, fname, kind, args = job
    F = Fmt(apf, fname)
    T = Fmt(apf, args[0]) if kind == "conv" else F
    if kind == "bin":
        cmd, mode = [apf, "bin", fname, args[0], args[1]], args[1]
        op = args[0]
        if op in ("add", "sub"):
            ref = lambda o: x_addsub(F, mode, o[0], o[1], op == "sub")
        elif op == "mul":
            ref = lambda o: x_mul(F, mode, o[0], o[1])
        elif op == "div":
            ref = lambda o: x_div(F, mode, o[0], o[1])
        else:
            ref = lambda o: x_remmod(F, op, o[0], o[1])
    elif kind == "fma":
        cmd = [apf, "fma", fname, args[0]]
        ref = lambda o: x_fma(F, args[0], o[0], o[1], o[2])
    elif kind == "rint":
        cmd = [apf, "rint", fname, args[0]]
        ref = lambda o: x_rint(F, args[0], o[0])
    elif kind == "next":
        cmd = [apf, "next", fname, args[0]]
        ref = lambda o: x_next(F, args[0] == "1", o[0])
    elif kind == "conv":
        cmd = [apf, "conv", fname, args[0], args[1]]
        ref = lambda o: x_conv(F, T, args[1], o[0])
    elif kind == "toint":
        cmd = [apf, "toint", fname, args[0], args[1], args[2]]
        ref = lambda o: x_toint(F, int(args[0]), args[1] == "1", args[2], o[0])
    elif kind == "fromint":
        cmd = [apf, "fromint", fname, args[0], args[1], args[2]]
        ref = lambda o: x_fromint(F, int(args[0]), args[1] == "1", args[2], o[0])
    elif kind == "cmp":
        cmd = [apf, "cmp", fname]
        ref = lambda o: x_cmp(F, o[0], o[1])
    elif kind == "scalbn":
        cmd = [apf, "scalbn", fname, args[0]]
        ref = lambda o: x_scalbn(F, args[0], o[0], o[1] - 4096)
    elif kind == "misc":
        cmd = [apf, "misc", fname]
        ref = lambda o: x_misc(F, o[0])
    else:
        raise SystemExit("unknown kind " + kind)
    tag = ".".join([fname, kind] + list(args))
    total = ok = wrong = signals = 0
    undoc = collections.Counter()
    undoc_ex = {}
    wrong_kinds = collections.Counter()
    flags = collections.Counter()
    flags_ex = {}
    flag_after = flag_before = flag_checked = 0
    bad = []
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)
    for line in proc.stdout:
        left, right = line.split("|")
        o = [int(x, 16) for x in left.split()]
        g = right.split()
        total += 1
        if kind in ("toint", "cmp", "misc"):
            if "!" in g:
                signals += 1
                wrong += 1
                wrong_kinds["signal %s" % g[-1]] += 1
                bad.append("%s | %s" % (left.strip(), " ".join(g)))
                continue
            if kind == "misc":
                e = ref(o)
                got = tuple(int(x) for x in g[:7]) + (" ".join(g[7:]),)
                if got == e:
                    ok += 1
                else:
                    wrong += 1
                    names = ("ilogb", "getExactLog2Abs", "isDenormal", "isSmallest", "isSmallestNormalized",
                             "isLargest", "isNormal", "getExactInverse")
                    for i in range(8):
                        if got[i] != e[i]:
                            wrong_kinds[names[i]] += 1
                    bad.append("%s | want %s got %s" % (left.strip(), " ".join(str(x) for x in e), " ".join(str(x) for x in got)))
                continue
            if kind == "cmp":
                e = ref(o)
                if int(g[0]) == e:
                    ok += 1
                else:
                    wrong += 1
                    wrong_kinds["compare"] += 1
                    bad.append("%s | want %d got %s" % (left.strip(), e, g[0]))
                continue
            e = ref(o)
            got = (int(g[0], 16), int(g[1]), int(g[2]))
            if got == e:
                ok += 1
            else:
                wrong += 1
                what = "integer" if got[0] != e[0] else ("status" if got[1] != e[1] else "isExact")
                wrong_kinds[what] += 1
                bad.append("%s | want %x %d %d got %x %d %d" % ((left.strip(),) + e + got))
            continue
        e = ref(o)
        if g[0] == "!":
            cat, bits, st = "!", int(g[1]), None
            signals += 1
        elif g[1] == "!":
            # the class was read, then the bit pattern could not be: "i ! 6"
            cat, bits, st = g[0] + "!", int(g[2]), None
            signals += 1
        else:
            cat, bits, st = g[0], int(g[1], 16), int(g[2])
        if e[0] == "U":
            key = (e[1], describe(T, cat, bits))
            undoc[key] += 1
            undoc_ex.setdefault(key, left.strip())
            continue
        if e[0] == "N":
            good = cat == "n" and bits in T.nans
            want = "NaN"
        else:
            good = cat == T.K[e[1]] and bits == e[1]
            want = "%x" % e[1]
        if not good:
            wrong += 1
            wk = "%s, got %s" % ("NaN" if e[0] == "N" else {ZERO: "zero", FIN: "finite", INF: "infinity"}[T.K[e[1]]],
                                 {"n": "NaN", "i": "infinity", "z": "zero", "f": "finite"}.get(cat, "signal"))
            wrong_kinds[wk] += 1
            bad.append("%s | want %s got %s %s" % (left.strip(), want, cat, g[1]))
            continue
        ok += 1
        if e[2] is not None and st is not None:
            flag_checked += 1
            if st == e[2][0]:
                flag_after += 1
            if st == e[2][1]:
                flag_before += 1
            if st != e[2][0] and st != e[2][1]:
                key = "want %d got %d" % (e[2][0], st)
                flags[key] += 1
                flags_ex.setdefault(key, left.strip())
        if kind == "conv" and st is not None and e[0] == "P" and e[2] is not None:
            if int(g[3]) != (1 if e[2][0] else 0):
                flags["losesInfo %s with status want %d" % (g[3], e[2][0])] += 1
                flags_ex.setdefault("losesInfo %s with status want %d" % (g[3], e[2][0]), left.strip())
    rc = proc.wait()
    if bad:
        with open(os.path.join(outdir, tag + ".bad"), "w") as f:
            f.write("\n".join(bad) + "\n")
    rec = {
        "run": tag, "total": total, "ok": ok, "wrong": wrong, "signals": signals, "exit": rc,
        "wrong_kinds": dict(wrong_kinds),
        "not_judged": [[k[0], k[1], v, undoc_ex[k]] for k, v in sorted(undoc.items())],
        "flags_checked": flag_checked, "flags_tiny_after": flag_after, "flags_tiny_before": flag_before,
        "flags_other": [[k, v, flags_ex[k]] for k, v in sorted(flags.items())],
    }
    with open(os.path.join(outdir, tag + ".json"), "w") as f:
        json.dump(rec, f, indent=1)
    return rec


def jobs_for(apf, outdir, formats, kinds, all_formats):
    out = []
    for f in formats:
        for k in kinds:
            if k == "bin":
                for op in ("add", "sub", "mul", "div"):
                    for m in MODES:
                        out.append((apf, outdir, f, "bin", (op, m)))
            elif k == "remmod":
                out.append((apf, outdir, f, "bin", ("rem", "ne")))
                out.append((apf, outdir, f, "bin", ("mod", "ne")))
            elif k == "rint":
                for m in MODES:
                    out.append((apf, outdir, f, "rint", (m,)))
            elif k == "next":
                out.append((apf, outdir, f, "next", ("0",)))
                out.append((apf, outdir, f, "next", ("1",)))
            elif k == "cmp":
                out.append((apf, outdir, f, "cmp", ()))
            elif k == "conv":
                for t in all_formats:
                    if t != f:
                        for m in MODES:
                            out.append((apf, outdir, f, "conv", (t, m)))
            elif k == "toint":
                for w in ("1", "4", "8", "16"):
                    for s in ("0", "1"):
                        for m in MODES:
                            out.append((apf, outdir, f, "toint", (w, s, m)))
            elif k == "fromint":
                for w in ("8", "12"):
                    for s in ("0", "1"):
                        for m in MODES:
                            out.append((apf, outdir, f, "fromint", (w, s, m)))
            elif k == "fma":
                for m in MODES:
                    out.append((apf, outdir, f, "fma", (m,)))
            elif k == "scalbn":
                for m in MODES:
                    out.append((apf, outdir, f, "scalbn", (m,)))
            elif k == "misc":
                out.append((apf, outdir, f, "misc", ()))
            else:
                raise SystemExit("unknown kind " + k)
    return out


def main():
    apf, outdir, formats, kinds = sys.argv[1], sys.argv[2], sys.argv[3].split(","), sys.argv[4].split(",")
    njobs = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    conv_targets = os.environ.get("CONV_TARGETS", "").split(",") if os.environ.get("CONV_TARGETS") else formats
    os.makedirs(outdir, exist_ok=True)
    jobs = jobs_for(apf, outdir, formats, kinds, conv_targets)
    with multiprocessing.Pool(njobs) as pool:
        recs = pool.map(run, jobs, chunksize=1)
    tot = collections.Counter()
    with open(os.path.join(outdir, "summary.tsv"), "a") as f:
        for r in recs:
            nj = sum(x[2] for x in r["not_judged"])
            f.write("%s\t%d\t%d\t%d\t%d\t%d\t%d\n" % (r["run"], r["total"], r["ok"], r["wrong"], nj, r["signals"], r["exit"]))
            tot["total"] += r["total"]
            tot["ok"] += r["ok"]
            tot["wrong"] += r["wrong"]
            tot["not judged"] += nj
            tot["signals"] += r["signals"]
            if r["wrong"] or r["exit"]:
                print("%-34s total %8d  wrong %7d  not judged %6d  %s" % (r["run"], r["total"], r["wrong"], nj, r["wrong_kinds"]))
    print("runs %d  " % len(recs) + "  ".join("%s %d" % (k, v) for k, v in tot.items()))


if __name__ == "__main__":
    main()
