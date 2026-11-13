"""The rules behind the IWLS 2025 contest functions ex180 to ex185: six functions of one half-precision number.

    ex180  1 / x        ex181  1 / x^2      ex182  1 / x^3      ex183  x^2      ex184  x^3      ex185  sqrt(x)

Input and output are IEEE 754 binary16: a sign bit, 5 exponent bits, 10 mantissa bits, with subnormals.
Each function is the exact real value rounded once, to nearest with ties to even. A value of 65520 or more is infinity.
A NaN operand comes back with its quiet bit set. The square root of a negative number, minus infinity included,
is the NaN fe00; the square root of -0 is -0.
"""
import math
from fractions import Fraction

NAMES = {180: "1/x", 181: "1/x^2", 182: "1/x^3", 183: "x^2", 184: "x^3", 185: "sqrt"}
INF = 0x7C00


def read(u):
    """-> (sign, kind, magnitude): kind is "nan", "inf" or "num"."""
    s, e, m = u >> 15, (u >> 10) & 31, u & 1023
    if e == 31:
        return s, ("nan" if m else "inf"), None
    if e == 0:
        return s, "num", Fraction(m, 1 << 24)
    return s, "num", Fraction(1024 + m, 1024) * Fraction(2) ** (e - 15)


def write(s, num, root=False):
    """Rounds the non-negative Fraction num, or its square root, to binary16 with sign s."""
    if num == 0:
        return s << 15
    # work in units of 2^-24, the subnormal spacing; q = floor(value * 2^(24 + g)) with g guard bits, plus a sticky
    g = 40
    if root:
        scaled = num * (1 << (2 * (24 + g)))
        q = math.isqrt(scaled.numerator // scaled.denominator)
        exact = (q * q == scaled)
    else:
        scaled = num * (1 << (24 + g))
        q = scaled.numerator // scaled.denominator
        exact = (scaled.denominator == 1)
    top = q.bit_length() - 1 - g                       # the value lies in [2^top, 2^(top+1)) units
    drop = g + max(top - 10, 0)                        # bits under the last kept one: 11 significant bits, or the grid
    kept, rest = q >> drop, q & ((1 << drop) - 1)
    half = 1 << (drop - 1)
    if rest > half or (rest == half and (not exact or kept & 1)):
        kept += 1
    units = kept << max(top - 10, 0)                   # the rounded value in subnormal units
    if units < 1024:
        return (s << 15) | units
    e = units.bit_length() - 10                        # units in [2^(e+9), 2^(e+10))
    if e >= 31:
        return (s << 15) | INF
    return (s << 15) | (e << 10) | ((units >> (e - 1)) - 1024)


def value(ex, u):
    s, kind, v = read(u)
    if kind == "nan":
        return u | 0x0200
    if ex == 185:
        if kind == "num" and v == 0:
            return u
        if s:
            return 0xFE00
        return INF if kind == "inf" else write(0, v, root=True)
    power = {180: 1, 181: 2, 182: 3, 183: 2, 184: 3}[ex]
    reciprocal = ex in (180, 181, 182)
    so = s if power % 2 else 0
    if kind == "inf":
        return (so << 15) | (0 if reciprocal else INF)
    if v == 0:
        return (so << 15) | (INF if reciprocal else 0)
    w = v ** power
    return write(so, 1 / w if reciprocal else w)
