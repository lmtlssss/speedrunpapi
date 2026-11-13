#!/usr/bin/env python3
"""Vectors for DIV on FP16ALT (bfloat16: 1 sign bit, 8 exponent bits, 7 fraction bits) with exact expected results.

usage: fp16alt_div_vectors.py [COUNT] [SEED] > fp16alt_div_vectors.txt

Each line is  a b rm result flags  in hexadecimal: the two operands and the expected result as 16-bit patterns, the
rounding mode (0 RNE, 1 RTZ, 2 RDN, 3 RUP, 4 RMM) and the expected flags {NV, DZ, OF, UF, NX}.
The quotient is formed as a rational number and rounded once. Tininess is detected after rounding, as RISC-V
specifies; UF is raised only together with NX. Every NaN result is the canonical quiet NaN 0x7fc0.
Every operand pair is written with all five rounding modes.
"""
import random
import sys
from fractions import Fraction

P, EMIN, EMAX, BIAS = 8, -126, 127, 127
QNAN, INF = 0x7fc0, 0x7f80
NV, DZ, OF, UF, NX = 16, 8, 4, 2, 1


def decode(w):
    """(kind, sign, magnitude): kind is 'nan', 'snan', 'inf' or 'num'."""
    s, e, f = w >> 15, (w >> 7) & 0xff, w & 0x7f
    if e == 0xff:
        return ("inf" if f == 0 else ("nan" if f & 0x40 else "snan")), s, None
    if e == 0:
        return "num", s, Fraction(f, 1 << 7) * Fraction(2) ** EMIN
    return "num", s, (1 + Fraction(f, 1 << 7)) * Fraction(2) ** (e - BIAS)


def to_integer(v, rm, negative):
    """Rounds the non-negative rational v to an integer in mode rm, for a value of the given sign."""
    n = v.numerator // v.denominator
    rest = v - n
    if rest == 0:
        return n
    half = Fraction(1, 2)
    if rm == 0:
        up = rest > half or (rest == half and n & 1)
    elif rm == 1:
        up = False
    elif rm == 2:
        up = negative
    elif rm == 3:
        up = not negative
    else:
        up = rest >= half
    return n + 1 if up else n


def round_pack(sign, mag, rm):
    """Exact magnitude mag > 0 -> (pattern, flags)."""
    e = mag.numerator.bit_length() - mag.denominator.bit_length()
    if Fraction(2) ** e > mag:
        e -= 1                                              # 2^e <= mag < 2^(e+1)
    unbounded = to_integer(mag / Fraction(2) ** (e - (P - 1)), rm, sign) * Fraction(2) ** (e - (P - 1))
    tiny = unbounded < Fraction(2) ** EMIN
    quantum = Fraction(2) ** (max(e, EMIN) - (P - 1))
    r = to_integer(mag / quantum, rm, sign) * quantum
    flags = NX if r != mag else 0
    if tiny and flags:
        flags |= UF
    if r >= Fraction(2) ** (EMAX + 1):                      # overflow: infinity or the largest finite number
        to_inf = rm in (0, 4) or (rm == 3 and not sign) or (rm == 2 and sign)
        return (sign << 15) | (INF if to_inf else INF - 1), OF | NX
    if r < Fraction(2) ** EMIN:
        frac = r / Fraction(2) ** (EMIN - (P - 1))
        assert frac.denominator == 1
        return (sign << 15) | int(frac), flags
    e2 = r.numerator.bit_length() - r.denominator.bit_length()
    if Fraction(2) ** e2 > r:
        e2 -= 1
    frac = (r / Fraction(2) ** e2 - 1) * (1 << 7)
    assert frac.denominator == 1
    return (sign << 15) | ((e2 + BIAS) << 7) | int(frac), flags


def divide(a, b, rm):
    ka, sa, ma = decode(a)
    kb, sb, mb = decode(b)
    s = sa ^ sb
    if "snan" in (ka, kb):
        return QNAN, NV
    if "nan" in (ka, kb):
        return QNAN, 0
    if ka == "inf":
        return (QNAN, NV) if kb == "inf" else ((s << 15) | INF, 0)
    if kb == "inf":
        return s << 15, 0
    if mb == 0:
        return (QNAN, NV) if ma == 0 else ((s << 15) | INF, DZ)
    if ma == 0:
        return s << 15, 0
    return round_pack(s, ma / mb, rm)


def pattern(sign, exponent_field, fraction):
    return (sign << 15) | (exponent_field << 7) | fraction


def operand_pairs(count, rnd):
    yield 0x0d00, 0x5080                                    # 2^-101 / 2^34 = 2^-135, a quarter of the smallest subnormal
    yield 0x0500, 0x5080                                    # 2^-117 / 2^34 = 2^-151
    yield 0xae47, 0xf447                                    # the operands of issue 169: 2^-140
    specials = [0x0000, 0x8000, 0x0001, 0x007f, 0x0080, 0x3f80, 0x7f7f, 0x7f80, 0xff80, 0x7fc0, 0x7fa0]
    for a in specials:
        for b in specials:
            yield a, b
    n = 0
    while n < count:
        kind = n % 4
        sa, sb = rnd.getrandbits(1), rnd.getrandbits(1)
        fa, fb = rnd.getrandbits(7), rnd.getrandbits(7)
        if kind == 0:                                       # quotient exponent between -156 and -124
            q = rnd.randint(-156, -124)
            eb = rnd.randint(max(1, 1 - q - 126 + 127 - 127), 254)
            ea = q + eb                                     # exponent fields: (ea - 127) - (eb - 127) = q
            if not 1 <= ea <= 254:
                ea, fa = 0, rnd.getrandbits(7) | 1          # subnormal dividend reaches the lowest quotients
                eb = rnd.randint(150, 254)
        elif kind == 1:                                     # around the overflow threshold
            eb = rnd.randint(1, 126)
            ea = min(254, eb + rnd.randint(125, 129))
        elif kind == 2:                                     # subnormal operands
            ea, eb = rnd.choice([0, rnd.randint(1, 254)]), rnd.choice([0, rnd.randint(1, 254)])
        else:
            ea, eb = rnd.randint(0, 254), rnd.randint(0, 254)
        yield pattern(sa, ea, fa), pattern(sb, eb, fb)
        n += 1


if __name__ == "__main__":
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 169)
    for a, b in operand_pairs(count, rnd):
        for rm in range(5):
            res, fl = divide(a, b, rm)
            print("%04x %04x %x %04x %02x" % (a, b, rm, res, fl))
