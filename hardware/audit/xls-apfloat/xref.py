#!/usr/bin/env python3
"""Exact reference for the functions of XLS's apfloat library, as its documentation states them.

IEEE 754 to nearest even on the bit layout sign | exponent | fraction, with the library's stated
differences: subnormal operands are zero where the function says so, subnormal results are flushed to
zero where it says so, and every NaN that comes out is the one canonical quiet NaN.

expect(what, args) returns the set of acceptable outputs for one call, or None where the case is not
judged. A result below the smallest normal number that rounds to it has two acceptable outputs, the
smallest normal number and zero: "flushed to zero" does not say which side of the rounding is meant.
"""


def round_up(q, r, d, mode):
    """1 when the magnitude q + r/d rounds up to q + 1. mode: ne, na, tz."""
    if r == 0 or mode == "tz":
        return 0
    if mode == "ne":
        return 1 if (2 * r > d or (2 * r == d and (q & 1))) else 0
    return 1 if 2 * r >= d else 0


class Fmt:
    def __init__(self, e, f):
        self.e, self.f = e, f
        self.w = 1 + e + f
        self.bias = (1 << (e - 1)) - 1
        self.emin = 1 - self.bias
        self.emax = self.bias
        self.p = f + 1
        self.expmax = (1 << e) - 1
        self.qnan = (self.expmax << f) | (1 << (f - 1))

    def dec(self, x):
        """(class, negative, M, E): value M * 2**E. class: z zero, s subnormal, n normal, i infinity, q NaN."""
        neg = (x >> (self.e + self.f)) & 1
        be = (x >> self.f) & self.expmax
        fr = x & ((1 << self.f) - 1)
        if be == self.expmax:
            return ("i" if fr == 0 else "q", neg, 0, 0)
        if be == 0:
            return ("z", neg, 0, 0) if fr == 0 else ("s", neg, fr, self.emin - self.f)
        return ("n", neg, (1 << self.f) | fr, be - self.bias - self.f)

    def daz(self, x):
        c, neg, m, e = self.dec(x)
        return ("z", neg, 0, 0) if c == "s" else (c, neg, m, e)

    def zero(self, neg):
        return neg << (self.e + self.f)

    def inf(self, neg):
        return (neg << (self.e + self.f)) | (self.expmax << self.f)

    def maxn(self, neg):
        return (neg << (self.e + self.f)) | (((self.expmax - 1) << self.f) | ((1 << self.f) - 1))

    def minn(self, neg):
        return (neg << (self.e + self.f)) | (1 << self.f)

    def is_nan(self, x):
        return self.dec(x)[0] == "q"

    def pack(self, neg, m, t):
        """The pattern of m * 2**t, m > 0, which fits the format exactly (normal or subnormal)."""
        top = m.bit_length() - 1 + t
        if top < self.emin:
            sh = t - (self.emin - self.f)
            assert sh >= 0
            return (neg << (self.e + self.f)) | (m << sh)
        sh = self.f - (m.bit_length() - 1)
        frac = (m << sh if sh >= 0 else m >> -sh) & ((1 << self.f) - 1)
        if sh < 0:
            assert m & ((1 << -sh) - 1) == 0
        return (neg << (self.e + self.f)) | ((top + self.bias) << self.f) | frac

    def rnd(self, num, den, x2, neg, mode, tiny):
        """num/den * 2**x2 > 0 with sign neg, rounded once.
        tiny: "flush" results below the smallest normal number become zero; "gradual" they are rounded
        on the subnormal grid; "flush_after" rounds on the subnormal grid first and then flushes."""
        e = num.bit_length() - den.bit_length()
        if e >= 0:
            if num < (den << e):
                e -= 1
        elif (num << -e) < den:
            e -= 1
        ex = e + x2

        def at(t):
            s = t - x2
            if s >= 0:
                d = den << s
                q, r = divmod(num, d)
            else:
                d = den
                q, r = divmod(num << -s, d)
            return q + round_up(q, r, d, mode)

        if ex >= self.emin:
            t = ex - self.p + 1
            m = at(t)
            if (m.bit_length() - 1 + t) > self.emax:
                return {self.maxn(neg)} if mode == "tz" else {self.inf(neg)}
            return {self.pack(neg, m, t)}
        t = self.emin - self.f
        m = at(t)
        if tiny == "flush":
            # IEEE with gradual underflow delivers the smallest normal number here; a processor in
            # flush-to-zero mode delivers zero unless the rounding to p digits reaches it as well.
            if m == (1 << self.f):
                return {self.zero(neg), self.minn(neg)}
            return {self.zero(neg)}
        if m == 0:
            return {self.zero(neg)}
        if tiny == "flush_after" and m < (1 << self.f):
            return {self.zero(neg)}
        return {self.pack(neg, m, t)}


def add(F, a, b, sub=False):
    ca, na, ma, ea = F.daz(a)
    cb, nb, mb, eb = F.daz(b)
    if ca == "q" or cb == "q":
        return {F.qnan}
    nb ^= 1 if sub else 0
    if ca == "i":
        if cb == "i" and na != nb:
            return {F.qnan}
        return {F.inf(na)}
    if cb == "i":
        return {F.inf(nb)}
    if ca == "z" and cb == "z":
        return {F.zero(na if na == nb else 0)}
    c = min(ea, eb)
    n = (-(ma << (ea - c)) if na else (ma << (ea - c))) + (-(mb << (eb - c)) if nb else (mb << (eb - c)))
    if n == 0:
        return {F.zero(0)}
    return F.rnd(abs(n), 1, c, 1 if n < 0 else 0, "ne", "flush")


def mul(F, a, b):
    ca, na, ma, ea = F.daz(a)
    cb, nb, mb, eb = F.daz(b)
    if ca == "q" or cb == "q":
        return {F.qnan}
    neg = na ^ nb
    if ca == "i" or cb == "i":
        if ca == "z" or cb == "z":
            return {F.qnan}
        return {F.inf(neg)}
    if ca == "z" or cb == "z":
        return {F.zero(neg)}
    return F.rnd(ma * mb, 1, ea + eb, neg, "ne", "flush")


def fma(F, a, b, c):
    ca, na, ma, ea = F.daz(a)
    cb, nb, mb, eb = F.daz(b)
    cc, nc, mc, ec = F.daz(c)
    if "q" in (ca, cb, cc):
        return {F.qnan}
    sab = na ^ nb
    if ca == "i" or cb == "i":
        if ca == "z" or cb == "z":
            return {F.qnan}
        if cc == "i" and nc != sab:
            return {F.qnan}
        return {F.inf(sab)}
    if cc == "i":
        return {F.inf(nc)}
    if ca == "z" or cb == "z":
        if cc == "z":
            return {F.zero(sab if sab == nc else 0)}
        return {c}
    pm, pe = ma * mb, ea + eb
    if cc == "z":
        return F.rnd(pm, 1, pe, sab, "ne", "flush")
    x = min(pe, ec)
    n = (-(pm << (pe - x)) if sab else (pm << (pe - x))) + (-(mc << (ec - x)) if nc else (mc << (ec - x)))
    if n == 0:
        return {F.zero(0)}
    return F.rnd(abs(n), 1, x, 1 if n < 0 else 0, "ne", "flush")


def integral(F, a, how, daz):
    """how: ceil, floor, trunc, even, away"""
    c, neg, m, e = F.daz(a) if daz else F.dec(a)
    if c == "q":
        return {F.qnan}
    if c in ("i", "z"):
        return {F.inf(neg) if c == "i" else F.zero(neg)}
    if e >= 0:
        return {a}
    d = 1 << -e
    q, r = divmod(m, d)
    if r:
        if how == "ceil":
            q += 0 if neg else 1
        elif how == "floor":
            q += 1 if neg else 0
        elif how == "even":
            q += round_up(q, r, d, "ne")
        elif how == "away":
            q += round_up(q, r, d, "na")
    if q == 0:
        return {F.zero(neg)}
    if q.bit_length() - 1 > F.emax:
        return None                       # the integer is above the largest finite number
    return {F.pack(neg, q, 0)}


def value(F, a):
    """A sortable value for comparisons, subnormals as zero: (-1 or 1 for infinities, fraction)."""
    from fractions import Fraction
    c, neg, m, e = F.daz(a)
    if c == "i":
        return (-1 if neg else 1, 0)
    if c == "z":
        return (0, Fraction(0))
    v = Fraction(m) * (Fraction(2) ** e)
    return (0, -v if neg else v)


def compare(F, a, b, op):
    if F.is_nan(a) or F.is_nan(b):
        return {0}
    x, y = value(F, a), value(F, b)
    r = {"eq": x == y, "gt": x > y, "gte": x >= y, "lte": x <= y, "lt": x < y}[op]
    return {1 if r else 0}


def trunc_int(F, a):
    """(class, signed integer truncated toward zero)"""
    c, neg, m, e = F.dec(a)
    if c in ("q", "i"):
        return c, neg, 0
    if c in ("z", "s"):
        return "v", neg, 0
    n = m << e if e >= 0 else m >> -e
    return "v", neg, -n if neg else n


def to_int(F, a, r, signed):
    lo, hi = (-(1 << (r - 1)), (1 << (r - 1)) - 1) if signed else (0, (1 << r) - 1)
    mask = (1 << r) - 1
    c, neg, n = trunc_int(F, a)
    if c == "q":
        return {0}
    if c == "i":
        return {(lo if neg else hi) & mask}
    return {max(lo, min(hi, n)) & mask}


def to_fixed(F, a, r):
    lo, hi = -(1 << (r - 1)), (1 << (r - 1)) - 1
    mask = (1 << r) - 1
    c, neg, n = trunc_int(F, a)
    if c in ("q", "i") or n < lo or n > hi:
        return {lo & mask}
    return {n & mask}


def from_fixed(F, x, n, mode):
    v = x - (1 << n) if x >> (n - 1) else x
    if v == 0:
        return {F.zero(0)}
    return F.rnd(abs(v), 1, 0, 1 if v < 0 else 0, mode, "flush")


def ldexp(F, a, k):
    c, neg, m, e = F.daz(a)
    if c == "q":
        return {F.qnan}
    if c == "i":
        return {F.inf(neg)}
    if c == "z":
        return {F.zero(neg)}
    return F.rnd(m, 1, e + k, neg, "ne", "flush")


def down(S, T, a, mode, tiny):
    c, neg, m, e = S.daz(a)
    if c == "q":
        return {T.qnan}
    if c == "i":
        return {T.inf(neg)}
    if c == "z":
        return {T.zero(neg)}
    return T.rnd(m, 1, e, neg, mode, tiny)


def up(S, T, a, daz):
    c, neg, m, e = S.daz(a) if daz else S.dec(a)
    if c == "q":
        return "nan"
    if c == "i":
        return {T.inf(neg)}
    if c == "z":
        return {T.zero(neg)}
    return {T.pack(neg, m, e)}


def expect(what, args):
    k = what[0]
    p = [int(x) for x in what[1:]]
    if k in ("add", "sub"):
        return add(Fmt(p[0], p[1]), args[0], args[1], k == "sub")
    if k == "mul":
        return mul(Fmt(p[0], p[1]), args[0], args[1])
    if k == "fma":
        return fma(Fmt(p[0], p[1]), args[0], args[1], args[2])
    if k in ("ceil", "ceildaz", "floor", "floordaz", "trunc", "round", "rounda"):
        how = {"ceil": "ceil", "ceildaz": "ceil", "floor": "floor", "floordaz": "floor", "trunc": "trunc",
               "round": "even", "rounda": "away"}[k]
        return integral(Fmt(p[0], p[1]), args[0], how, k.endswith("daz"))
    if k in ("eq", "gt", "gte", "lte", "lt"):
        return compare(Fmt(p[0], p[1]), args[0], args[1], k)
    if k == "toint":
        return to_int(Fmt(p[0], p[1]), args[0], p[2], True)
    if k == "touint":
        return to_int(Fmt(p[0], p[1]), args[0], p[2], False)
    if k == "tofixed":
        return to_fixed(Fmt(p[0], p[1]), args[0], p[2])
    if k == "fromfixed_rne":
        return from_fixed(Fmt(p[0], p[1]), args[0], p[2], "ne")
    if k == "fromfixed_rz":
        return from_fixed(Fmt(p[0], p[1]), args[0], p[2], "tz")
    if k == "ldexp":
        e = args[1] - 256 if args[1] >= 128 else args[1]
        return ldexp(Fmt(p[0], p[1]), args[0], e)
    if k in ("down_rne", "down_even", "down_away"):
        S, T = Fmt(p[0], p[1]), Fmt(p[2], p[3])
        if k == "down_rne":
            return down(S, T, args[0], "ne", "flush_after")
        return down(S, T, args[0], "ne" if k == "down_even" else "na", "gradual")
    if k in ("up", "updaz"):
        return up(Fmt(p[0], p[1]), Fmt(p[2], p[3]), args[0], k == "updaz")
    raise ValueError(what)
