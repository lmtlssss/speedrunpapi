"""The rules behind the IWLS 2025 contest functions ex160 to ex179: twenty operations on 8-bit floating-point numbers.

A number is a sign bit, EB exponent bits and MB mantissa bits, in one of four formats:

    ex160 - ex164    1-2-5        ex165 - ex169    1-3-4        ex170 - ex174    1-4-3        ex175 - ex179    1-5-2

Within a format the five functions are add, multiply, divide, hypotenuse and power, in that order.
The 16 inputs are two numbers. For add, multiply and hypotenuse the first operand is the low byte;
for divide and power the first operand is the high byte (high / low, high ^ low).

Reading a number
    exponent field 0             subnormal: mantissa / 2^MB * 2^(1 - bias), which includes zero
    exponent field all ones      infinity, whatever the mantissa
    otherwise                    (1 + mantissa / 2^MB) * 2^(exponent - bias),   bias = 2^(EB-1) - 1

Writing a result
    invalid (0 * inf, inf - inf, 0 / 0, inf / inf, a negative base with a non-integer power): sign 1, exponent all ones, mantissa 0
    at or above 2^(all ones - bias) after rounding: infinity with the sign of the result
    otherwise rounded to nearest on the format's grid, ties away from zero
    under one unit of the subnormal grid: rounded to one significant bit first, so 3/4 of a unit and more
    gives one unit and less gives zero

Zero results carry the usual signs: a product or quotient the exclusive-or of the operand signs, a sum of two
negative zeros negative, any other zero sum positive.
"""
import math
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
FORMATS = {"1-2-5": (2, 5), "1-3-4": (3, 4), "1-4-3": (4, 3), "1-5-2": (5, 2)}
OPS = ["add", "mul", "div", "hypot", "pow"]
INF, NAN = "inf", "nan"


def function(ex):
    """ex -> (operation, EB, MB, first operand in the high byte)."""
    fmt = list(FORMATS.values())[(ex - 160) // 5]
    name = OPS[(ex - 160) % 5]
    return name, fmt[0], fmt[1], name in ("div", "pow")


def read(u, eb, mb):
    """8-bit code -> (sign, magnitude as a Fraction or INF)."""
    s, e, m = u >> (eb + mb), (u >> mb) & ((1 << eb) - 1), u & ((1 << mb) - 1)
    bias, top = (1 << (eb - 1)) - 1, (1 << eb) - 1
    if e == top:
        return s, INF
    if e == 0:
        return s, Fraction(m, 1 << mb) * Fraction(2) ** (1 - bias)
    return s, Fraction((1 << mb) + m, 1 << mb) * Fraction(2) ** (e - bias)


def write(s, a, eb, mb):
    """sign and magnitude (Fraction >= 0, INF or NAN) -> 8-bit code."""
    bias, top = (1 << (eb - 1)) - 1, (1 << eb) - 1
    if a == NAN:
        return (1 << (eb + mb)) | (top << mb)
    if a == INF:
        return (s << (eb + mb)) | (top << mb)
    if a == 0:
        return s << (eb + mb)
    E = a.numerator.bit_length() - a.denominator.bit_length()        # 2^E <= a < 2^(E+1)
    while Fraction(2) ** E > a:
        E -= 1
    while Fraction(2) ** (E + 1) <= a:
        E += 1
    emin = 1 - bias
    p = max(mb - max(emin - E, 0), 0)                                # fraction bits this binade has, never below 0
    scaled = a / Fraction(2) ** (E - p)
    sig = scaled.numerator // scaled.denominator
    if scaled - sig >= Fraction(1, 2):                               # nearest, ties away from zero
        sig += 1
    units = sig * Fraction(2) ** (E - p) / Fraction(2) ** (emin - mb)
    m = units.numerator // units.denominator                         # in units of the subnormal grid
    if m < (1 << mb):
        return (s << (eb + mb)) | m
    e = 1
    while m >= (1 << (mb + 1)):
        m >>= 1
        e += 1
    if e >= top:
        return (s << (eb + mb)) | (top << mb)
    return (s << (eb + mb)) | (e << mb) | (m - (1 << mb))


def operate(name, x, y, eb, mb):
    sx, vx = read(x, eb, mb)
    sy, vy = read(y, eb, mb)
    if name == "add":
        if vx == INF and vy == INF:
            return write(sx, INF, eb, mb) if sx == sy else write(1, NAN, eb, mb)
        if vx == INF or vy == INF:
            return write(sx if vx == INF else sy, INF, eb, mb)
        t = (-vx if sx else vx) + (-vy if sy else vy)
        return write(sx & sy if t == 0 else (1 if t < 0 else 0), abs(t), eb, mb)
    if name == "mul":
        if vx == INF or vy == INF:
            other = vy if vx == INF else vx
            return write(1, NAN, eb, mb) if other == 0 else write(sx ^ sy, INF, eb, mb)
        return write(sx ^ sy, vx * vy, eb, mb)
    if name == "div":
        if vx == INF:
            return write(1, NAN, eb, mb) if vy == INF else write(sx ^ sy, INF, eb, mb)
        if vy == INF:
            return write(sx ^ sy, Fraction(0), eb, mb)
        if vy == 0:
            return write(1, NAN, eb, mb) if vx == 0 else write(sx ^ sy, INF, eb, mb)
        return write(sx ^ sy, vx / vy, eb, mb)
    if name == "hypot":
        if vx == INF or vy == INF:
            return write(0, INF, eb, mb)
        t = vx * vx + vy * vy                                        # exact; the root is taken to 2^-80
        return write(0, Fraction(math.isqrt((t.numerator << 160) // t.denominator), 1 << 80), eb, mb)
    if name == "pow":
        return power(sx, vx, sy, vy, eb, mb)
    raise ValueError(name)


def exact_root(v, j):
    """The 2^j-th root of the Fraction v when it is rational, else None."""
    for _ in range(j):
        n, d = math.isqrt(v.numerator), math.isqrt(v.denominator)
        if n * n != v.numerator or d * d != v.denominator:
            return None
        v = Fraction(n, d)
    return v


def power(sx, vx, sy, vy, eb, mb):
    """x^y with the special cases of the C library's pow, the value rounded once to the format."""
    one = write(0, Fraction(1), eb, mb)
    if vy == 0:
        return one                                                   # x^0 = 1 for every x
    if vx == 1 and not sx:
        return one                                                   # 1^y = 1 for every y
    y_int = vy != INF and vy.denominator == 1
    y_odd = y_int and vy.numerator % 2 == 1
    if vx == 1 and sx:                                               # (-1)^y
        if vy == INF:
            return one
        return write(1 if y_odd else 0, Fraction(1), eb, mb) if y_int else write(1, NAN, eb, mb)
    if vy == INF:
        grows = (vx == INF or vx > 1) != bool(sy)
        return write(0, INF if grows else Fraction(0), eb, mb)
    if vx == INF or vx == 0:
        grows = (vx == INF) != bool(sy)
        return write(1 if (sx and y_odd) else 0, INF if grows else Fraction(0), eb, mb)
    if sx and not y_int:
        return write(1, NAN, eb, mb)
    sign = 1 if (sx and y_odd) else 0
    log = (Decimal(vx.numerator).ln() - Decimal(vx.denominator).ln()) * Decimal(vy.numerator) / Decimal(vy.denominator)
    if sy:
        log = -log
    if log > 200:
        return write(sign, INF, eb, mb)
    if log < -200:
        return write(sign, Fraction(0), eb, mb)
    j = vy.denominator.bit_length() - 1                              # y = k / 2^j
    root = exact_root(vx, j)
    if root is not None:                                             # the value is rational: exact, so ties are seen
        r = root ** vy.numerator
        return write(sign, 1 / r if sy else r, eb, mb)
    return write(sign, Fraction(log.exp()), eb, mb)                  # irrational: 60 digits decide the rounding


def value(ex, u):
    """The 8-bit output of function ex on the 16-bit input word u (bit 0 is the first input)."""
    name, eb, mb, high_first = function(ex)
    lo, hi = u & 255, u >> 8
    return operate(name, hi, lo, eb, mb) if high_first else operate(name, lo, hi, eb, mb)
