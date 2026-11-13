#!/usr/bin/env python3
"""Vectors for ADDS from FP64 into FP32: op[1] + op[2], both binary64, the exact sum rounded once to binary32.

usage: adds_narrow_vectors.py [COUNT] [SEED]
Each line: b c rm result flags (hex): two 64-bit operands, rounding mode, expected 32-bit result, flags {NV,DZ,OF,UF,NX}.
"""
import random
import sys
from fractions import Fraction

NV, DZ, OF, UF, NX = 16, 8, 4, 2, 1


def dec64(w):
    s, e, f = w >> 63, (w >> 52) & 0x7ff, w & ((1 << 52) - 1)
    if e == 0x7ff:
        return ("inf" if f == 0 else ("nan" if f >> 51 else "snan")), s, None
    if e == 0:
        return "num", s, Fraction(f, 1 << 52) * Fraction(2) ** -1022
    return "num", s, (1 + Fraction(f, 1 << 52)) * Fraction(2) ** (e - 1023)


def to_integer(v, rm, negative):
    n = v.numerator // v.denominator
    rest = v - n
    if rest == 0:
        return n
    half = Fraction(1, 2)
    up = {0: rest > half or (rest == half and n & 1), 1: False, 2: negative, 3: not negative, 4: rest >= half}[rm]
    return n + 1 if up else n


def pack32(sign, mag, rm):
    P, EMIN, EMAX = 24, -126, 127
    e = mag.numerator.bit_length() - mag.denominator.bit_length()
    if Fraction(2) ** e > mag:
        e -= 1
    unbounded = to_integer(mag / Fraction(2) ** (e - (P - 1)), rm, sign) * Fraction(2) ** (e - (P - 1))
    tiny = unbounded < Fraction(2) ** EMIN
    quantum = Fraction(2) ** (max(e, EMIN) - (P - 1))
    r = to_integer(mag / quantum, rm, sign) * quantum
    flags = NX if r != mag else 0
    if tiny and flags:
        flags |= UF
    if r >= Fraction(2) ** (EMAX + 1):
        to_inf = rm in (0, 4) or (rm == 3 and not sign) or (rm == 2 and sign)
        return (sign << 31) | (0x7f800000 if to_inf else 0x7f7fffff), OF | NX
    if r < Fraction(2) ** EMIN:
        return (sign << 31) | int(r / Fraction(2) ** (EMIN - (P - 1))), flags
    e2 = r.numerator.bit_length() - r.denominator.bit_length()
    if Fraction(2) ** e2 > r:
        e2 -= 1
    return (sign << 31) | ((e2 + 127) << 23) | int((r / Fraction(2) ** e2 - 1) * (1 << 23)), flags


def adds(b, c, rm):
    kb, sb, mb = dec64(b)
    kc, sc, mc = dec64(c)
    if "snan" in (kb, kc):
        return 0x7fc00000, NV
    if "nan" in (kb, kc):
        return 0x7fc00000, 0
    if kb == "inf" or kc == "inf":
        if kb == "inf" and kc == "inf" and sb != sc:
            return 0x7fc00000, NV
        return ((sb if kb == "inf" else sc) << 31) | 0x7f800000, 0
    total = (-mb if sb else mb) + (-mc if sc else mc)
    if total == 0:
        if mb == 0 and mc == 0 and sb == sc:
            return sb << 31, 0
        return (1 << 31) if rm == 2 else 0, 0
    return pack32(1 if total < 0 else 0, abs(total), rm)


if __name__ == "__main__":
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    pairs = [(0, 0x37e0000000000000), (0, 0x37f0000000000000)]
    for n in range(count):
        kind = n % 4
        if kind == 0:                       # both addends around and below the smallest binary32 normal, 2^-126
            eb, ec = rnd.randint(1023 - 160, 1023 - 120), rnd.randint(1023 - 160, 1023 - 120)
        elif kind == 1:                     # around the binary32 overflow threshold
            eb, ec = rnd.randint(1023 + 120, 1023 + 130), rnd.randint(1023 + 100, 1023 + 130)
        elif kind == 2:                     # ordinary magnitudes, close exponents
            eb = rnd.randint(1023 - 60, 1023 + 60)
            ec = eb + rnd.randint(-30, 30)
        else:
            eb, ec = rnd.randint(1, 2046), rnd.randint(1, 2046)
        b = (rnd.getrandbits(1) << 63) | (eb << 52) | rnd.getrandbits(52)
        c = (rnd.getrandbits(1) << 63) | (ec << 52) | rnd.getrandbits(52)
        pairs.append((b, c))
    for b, c in pairs:
        for rm in range(5):
            res, fl = adds(b, c, rm)
            print("%016x %016x %x %08x %02x" % (b, c, rm, res, fl))
