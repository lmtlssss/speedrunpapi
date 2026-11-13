"""What the fourteen circuits compute, as functions on 64-bit patterns.

The float functions are IEEE 754 binary64 in round to nearest even, with the NaN rules of Berkeley SoftFloat 2,
from which the published circuits were compiled:

    default NaN            7fffffffffffffff
    a NaN operand          comes back with its quiet bit set
    two NaN operands       the second, unless only the first is signalling

Python floats are binary64 with round to nearest even, so the arithmetic itself is the host's.
"""
import math
import struct
from fractions import Fraction

M64 = (1 << 64) - 1
SIGN = 1 << 63
QUIET = 1 << 51
INF = 0x7ff0000000000000
DEFAULT_NAN = 0x7fffffffffffffff


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def value(u):
    return struct.unpack("<d", struct.pack("<Q", u))[0]


def is_nan(u):
    return (u & ~SIGN & M64) > INF


def is_snan(u):
    return ((u >> 51) & 0xfff) == 0xffe and (u & 0x0007ffffffffffff) != 0


def propagate(a, b):
    if is_snan(b):
        return b | QUIET
    if is_snan(a):
        return a | QUIET
    if is_nan(b):
        return b | QUIET
    return a | QUIET


def fp_add(a, b):
    if is_nan(a) or is_nan(b):
        return propagate(a, b)
    ainf, binf = (a & ~SIGN & M64) == INF, (b & ~SIGN & M64) == INF
    if ainf and binf:
        return a if (a ^ b) & SIGN == 0 else DEFAULT_NAN
    if ainf:
        return a
    if binf:
        return b
    return bits(value(a) + value(b))


def fp_mul(a, b):
    if is_nan(a) or is_nan(b):
        return propagate(a, b)
    sign = (a ^ b) & SIGN
    am, bm = a & ~SIGN & M64, b & ~SIGN & M64
    if am == INF or bm == INF:
        return DEFAULT_NAN if am == 0 or bm == 0 else sign | INF
    return bits(value(a) * value(b))


def fp_div(a, b):
    """first operand / second operand"""
    if is_nan(a) or is_nan(b):
        return propagate(a, b)
    sign = (a ^ b) & SIGN
    am, bm = a & ~SIGN & M64, b & ~SIGN & M64
    if am == INF:
        return DEFAULT_NAN if bm == INF else sign | INF
    if bm == INF:
        return sign
    if bm == 0:
        return DEFAULT_NAN if am == 0 else sign | INF
    return bits(value(a) / value(b))


def fp_sqrt(a):
    if is_nan(a):
        return a | QUIET
    if (a & ~SIGN & M64) == 0:
        return a
    if a & SIGN:
        return DEFAULT_NAN
    if a == INF:
        return a
    return bits(math.sqrt(value(a)))


def fp_eq(a, b):
    """1 in bit 0 when equal; +0 equals -0; a NaN equals nothing"""
    if is_nan(a) or is_nan(b):
        return 0
    return 1 if (a == b or ((a | b) & ~SIGN & M64) == 0) else 0


def fp_lt(a, b):
    """1 in bit 0 when the first operand is less than the second"""
    if is_nan(a) or is_nan(b):
        return 0
    return 1 if value(a) < value(b) else 0


def fp_f2i(a):
    """to a signed 64-bit integer, nearest even; a NaN and anything too large give 7fff..., too negative 8000..."""
    if is_nan(a):
        return 0x7fffffffffffffff
    if (a & ~SIGN & M64) == INF:
        return 0x8000000000000000 if a & SIGN else 0x7fffffffffffffff
    x = Fraction(value(a))
    n = math.floor(x)
    r = x - n
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and (n & 1)):
        n += 1
    if n > (1 << 63) - 1:
        return 0x7fffffffffffffff
    if n < -(1 << 63):
        return 0x8000000000000000
    return n & M64


def fp_i2f(a):
    """a signed 64-bit integer to the nearest double, ties to even"""
    return bits(float(a - (1 << 64) if a & SIGN else a))


def fp_floor(a):
    if is_nan(a):
        return a | QUIET
    if (a & ~SIGN & M64) in (0, INF):
        return a
    r = math.floor(value(a))
    return a & SIGN if r == 0 else bits(float(r))


def fp_ceil(a):
    if is_nan(a):
        return a | QUIET
    if (a & ~SIGN & M64) in (0, INF):
        return a
    r = math.ceil(value(a))
    return a & SIGN if r == 0 else bits(float(r))          # the ceiling of a negative fraction is -0


def signed(x):
    return x - (1 << 64) if x & SIGN else x


def mult64(a, b):
    return (a * b) & M64


def mult2_64(a, b):
    """the first output word is the high half of the product, the second the low half"""
    p = a * b
    return (p >> 64) | ((p & M64) << 64)


def udivide64(a, b):
    """a zero divisor gives all ones"""
    return M64 if b == 0 else a // b


def divide64(a, b):
    """signed, truncating toward zero, modulo 2^64. A zero divisor gives -1 for a dividend that is not negative,
    1 for a negative one and 2 for -2^63, as the published circuit does."""
    x, y = signed(a), signed(b)
    if y == 0:
        if x == -(1 << 63):
            return 2
        return M64 if x >= 0 else 1
    q = abs(x) // abs(y)
    return (-q if (x < 0) != (y < 0) else q) & M64


def mod_add_512(a, b, p):
    """a + b, less p once when the sum is at least p; the low 512 bits"""
    s = a + b
    return (s - p if s >= p else s) & ((1 << 512) - 1)


def lsss_to_gc(a, b, p):
    """With s = a + b and h = p >> 1: s less p once when s >= h and once more when s >= p + h; the low 64 bits.
    For a and b below p this is the sum modulo p, read as a signed number between -p/2 and p/2."""
    s = a + b
    h = p >> 1
    k = (1 if s >= h else 0) + (1 if s >= p + h else 0)
    return (s - k * p) & M64


# name: (widths of the operands, rule)
FUNCTIONS = {
    "FP-add": ((64, 64), fp_add), "FP-mul": ((64, 64), fp_mul), "FP-div": ((64, 64), fp_div), "FP-sqrt": ((64,), fp_sqrt),
    "FP-eq": ((64, 64), fp_eq), "FP-lt": ((64, 64), fp_lt), "FP-f2i": ((64,), fp_f2i), "FP-i2f": ((64,), fp_i2f),
    "FP-floor": ((64,), fp_floor), "FP-ceil": ((64,), fp_ceil),
    "mult64": ((64, 64), mult64), "mult2_64": ((64, 64), mult2_64), "udivide64": ((64, 64), udivide64),
    "divide64": ((64, 64), divide64),
    "ModAdd512": ((512, 512, 512), mod_add_512), "LSSS_to_GC": ((512, 512, 512), lsss_to_gc),
}
