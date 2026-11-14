# The operations of the VHDL float package in exact arithmetic, for any binary format and the four
# rounding styles, with the vectors and the comparison.
#
#   python3 exact.py gen SEED N EW,FW [EW,FW ...] > vectors.txt     N vectors per operation, format and style
#   python3 exact.py all EW,FW [op ...] > vectors.txt               every operand of a small format
#   python3 exact.py run vectors.txt results.txt -- CMD ...         runs the testbench; {vec}, {out}, {skip} in CMD
#   python3 exact.py check vectors.txt results.txt                  the table and the first mismatches
#
# A value is a sign and a fraction of two integers, so nothing here rounds until the one place that should.
import itertools
import os
import random
import subprocess
import sys
from fractions import Fraction
from math import isqrt

NEAREST, ZERO, NEGINF, INF = 0, 1, 2, 3
STYLE = ["round_nearest", "round_zero", "round_neginf", "round_inf"]
OPS = ["add", "subtract", "multiply", "divide", "sqrt", "mac", "reciprocal", "resize", "to_float",
       "to_signed", "to_unsigned", "to_integer", "to_float_integer", "dividebyp2", "scalb"]
FROM_INT = ("to_float", "to_float_integer")             # from a signed vector, from an integer
TO_INT = ("to_signed", "to_unsigned", "to_integer")
NAN = "nan"


class Fmt:
    def __init__(self, ew, fw):
        self.ew, self.fw, self.w = ew, fw, ew + fw + 1
        self.bias = (1 << (ew - 1)) - 1
        self.emin, self.emax = 1 - self.bias, self.bias
        self.top = (1 << ew) - 1                        # exponent field of infinity and NaN

    def inf(self, sign):
        return (sign << (self.w - 1)) | (self.top << self.fw)

    def largest(self, sign):
        return self.inf(sign) - 1

    def zero(self, sign):
        return sign << (self.w - 1)


def decode(f, bits):
    """-> NAN, or (sign, 'inf'), or (sign, Fraction)."""
    sign = bits >> (f.w - 1)
    e = (bits >> f.fw) & f.top
    m = bits & ((1 << f.fw) - 1)
    if e == f.top:
        return NAN if m else (sign, "inf")
    if e == 0:
        return (sign, Fraction(m) * Fraction(2) ** (f.emin - f.fw))
    return (sign, Fraction((1 << f.fw) + m) * Fraction(2) ** (e - f.bias - f.fw))


def floor_log2(v):
    e = v.numerator.bit_length() - v.denominator.bit_length()
    return e if Fraction(2) ** e <= v else e - 1


def finish(f, sign, style, n, qexp, state):
    """n units of 2**qexp plus a rest: state 0 none, 1 below half a unit, 2 half, 3 above half."""
    up = ((style == NEAREST and (state == 3 or (state == 2 and n & 1)))
          or (style == INF and state and not sign) or (style == NEGINF and state and sign))
    n += 1 if up else 0
    if n == 1 << (f.fw + 1):                            # carried into the next binade
        n, qexp = n >> 1, qexp + 1
    if qexp + f.fw > f.emax:                            # too large for the format
        if style == NEAREST or (style == INF and not sign) or (style == NEGINF and sign):
            return f.inf(sign)
        return f.largest(sign)
    if n < 1 << f.fw:                                   # subnormal or zero: qexp is emin - fw
        return f.zero(sign) | n
    return f.zero(sign) | ((qexp + f.fw + f.bias) << f.fw) | (n - (1 << f.fw))


def rounded(f, sign, v, style):
    """The positive fraction v in the format."""
    qexp = max(floor_log2(v), f.emin) - f.fw
    q = Fraction(2) ** qexp
    n = int(v // q)
    rest = v - n * q
    state = 0 if rest == 0 else 1 if 2 * rest < q else 2 if 2 * rest == q else 3
    return finish(f, sign, style, n, qexp, state)


def rounded_root(f, v, style):
    """The square root of the positive fraction v in the format."""
    qexp = max(floor_log2(v) // 2, f.emin) - f.fw
    t = v / Fraction(4) ** qexp                         # the root is sqrt(t) units of 2**qexp
    n = isqrt(int(t // 1))
    if n * n == t:
        state = 0
    else:
        half = Fraction((2 * n + 1) ** 2, 4)
        state = 1 if t < half else 2 if t == half else 3
    return finish(f, 0, style, n, qexp, state)


def to_int(sign, v, style):
    """The fraction v with its sign, as an integer."""
    n = int(v // 1)
    rest = v - n
    state = 0 if rest == 0 else 1 if 2 * rest < 1 else 2 if 2 * rest == 1 else 3
    up = ((style == NEAREST and (state == 3 or (state == 2 and n & 1)))
          or (style == INF and state and not sign) or (style == NEGINF and state and sign))
    n += 1 if up else 0
    return -n if sign else n


def zero_sign(s1, s2, style):
    """Sign of an exact zero sum of two terms with the signs s1 and s2 (IEEE 754-2008, 6.3)."""
    if s1 == s2:
        return s1
    return 1 if style == NEGINF else 0


def add(f, x, y, style):
    if x == NAN or y == NAN:
        return NAN
    (sx, vx), (sy, vy) = x, y
    if vx == "inf" or vy == "inf":
        if vx == "inf" and vy == "inf" and sx != sy:
            return NAN
        return f.inf(sx if vx == "inf" else sy)
    total = (-vx if sx else vx) + (-vy if sy else vy)
    if total == 0:
        return f.zero(zero_sign(sx, sy, style))
    return rounded(f, int(total < 0), abs(total), style)


def multiply(f, x, y, style):
    if x == NAN or y == NAN:
        return NAN
    (sx, vx), (sy, vy) = x, y
    s = sx ^ sy
    if vx == "inf" or vy == "inf":
        return NAN if vx == 0 or vy == 0 else f.inf(s)
    if vx == 0 or vy == 0:
        return f.zero(s)
    return rounded(f, s, vx * vy, style)


def divide(f, x, y, style):
    if x == NAN or y == NAN:
        return NAN
    (sx, vx), (sy, vy) = x, y
    s = sx ^ sy
    if vx == "inf":
        return NAN if vy == "inf" else f.inf(s)
    if vy == "inf":
        return f.zero(s)
    if vy == 0:
        return NAN if vx == 0 else f.inf(s)
    if vx == 0:
        return f.zero(s)
    return rounded(f, s, vx / vy, style)


def sqrt(f, x, style):
    if x == NAN:
        return NAN
    s, v = x
    if v == 0:
        return f.zero(s)
    if s:
        return NAN
    return f.inf(0) if v == "inf" else rounded_root(f, v, style)


def mac(f, x, y, c, style):
    """x * y + c with one rounding."""
    if x == NAN or y == NAN or c == NAN:
        return NAN
    (sx, vx), (sy, vy), (sc, vc) = x, y, c
    sp = sx ^ sy
    if vx == "inf" or vy == "inf":
        if vx == 0 or vy == 0 or (vc == "inf" and sc != sp):
            return NAN
        return f.inf(sp)
    if vc == "inf":
        return f.inf(sc)
    vp = vx * vy
    total = (-vp if sp else vp) + (-vc if sc else vc)
    if total == 0:
        return f.zero(zero_sign(sp, sc, style))
    return rounded(f, int(total < 0), abs(total), style)


def resize(f2, x, style):
    if x == NAN:
        return NAN
    s, v = x
    if v == "inf":
        return f2.inf(s)
    return f2.zero(s) if v == 0 else rounded(f2, s, v, style)


def expected(op, st, f, p1, p2, operands):
    """-> the result bits, NAN, or None where the package is left to itself (out of the integer's range)."""
    name = OPS[op]
    if name in FROM_INT:
        n = operands[0] - (1 << p1) if operands[0] >> (p1 - 1) else operands[0]
        return f.zero(0) if n == 0 else rounded(f, int(n < 0), Fraction(abs(n)), st)
    x = decode(f, operands[0])
    if name in ("add", "subtract"):
        y = decode(f, operands[1])
        if name == "subtract" and y != NAN:
            y = (y[0] ^ 1, y[1])
        return add(f, x, y, st)
    if name == "multiply":
        return multiply(f, x, decode(f, operands[1]), st)
    if name in ("divide", "dividebyp2"):
        return divide(f, x, decode(f, operands[1]), st)
    if name == "scalb":                                 # x * 2**p1
        if x == NAN or x[1] == "inf":
            return NAN if x == NAN else f.inf(x[0])
        far = 2 * (f.emax - f.emin + f.fw) + 8          # past this the result has left the format either way
        n = max(-far, min(far, p1))
        return f.zero(x[0]) if x[1] == 0 else rounded(f, x[0], x[1] * Fraction(2) ** n, st)
    if name == "sqrt":
        return sqrt(f, x, st)
    if name == "mac":
        return mac(f, x, decode(f, operands[1]), decode(f, operands[2]), st)
    if name == "reciprocal":
        return divide(f, (0, Fraction(1)), x, st)
    if name == "resize":
        return resize(Fmt(p1, p2), x, st)
    if x == NAN or x[1] == "inf":
        return None
    n = to_int(x[0], x[1], st)
    if name == "to_signed":
        return n & ((1 << p1) - 1) if -(1 << (p1 - 1)) <= n < 1 << (p1 - 1) else None
    if name == "to_unsigned":
        return n if 0 <= n < 1 << p1 else None
    return n if abs(x[1]) < 1 << 30 else None           # to_integer


# ---- operands -------------------------------------------------------------------------------------------

def fraction_bits(f, rng):
    full = (1 << f.fw) - 1
    k = rng.random()
    if k < 0.35:
        return rng.getrandbits(f.fw)
    if k < 0.50:
        return 0
    if k < 0.60:
        return max(0, full - rng.randrange(4))
    if k < 0.70:
        return min(full, rng.randrange(4))
    if k < 0.80:
        return 1 << rng.randrange(f.fw)
    if k < 0.90:
        return (rng.getrandbits(f.fw) >> (f.fw // 2)) << (f.fw // 2)
    return rng.getrandbits(f.fw) | ((1 << rng.randrange(1, f.fw + 1)) - 1)


def pick(f, rng, positive=False):
    """A number of the format, weighted toward the places arithmetic breaks."""
    sign = 0 if positive else rng.getrandbits(1)
    k = rng.random()
    if k < 0.03:
        return f.zero(sign) | rng.choice([0, f.top << f.fw, (f.top << f.fw) | 1, 1, f.bias << f.fw])
    if k < 0.33:
        e = rng.randrange(f.top)
    elif k < 0.50:
        e = rng.randrange(min(4, f.top))
    elif k < 0.63:
        e = max(0, f.top - 1 - rng.randrange(4))
    else:
        e = min(f.top - 1, max(0, f.bias + rng.randrange(-f.fw - 3, f.fw + 4)))
    return f.zero(sign) | (e << f.fw) | fraction_bits(f, rng)


def with_exponent(f, bits, e):
    e = min(f.top - 1, max(0, e))
    return (bits & ~(f.top << f.fw)) | (e << f.fw)


def field(f, bits):
    return (bits >> f.fw) & f.top


def near(f, bits, rng):
    """A neighbour of the number, a few units of the last place away."""
    mag = bits & ((1 << (f.w - 1)) - 1)
    mag = min(f.inf(0) - 1, max(0, mag + rng.randrange(-3, 4)))
    return (bits & f.zero(1)) | mag


def operands(name, f, p1, p2, rng):
    a = pick(f, rng)
    k = rng.random()
    if name in ("add", "subtract"):
        if k < 0.40:
            b = pick(f, rng)
        elif k < 0.60:                                  # close in size: cancellation and carries
            b = near(f, a, rng) ^ (f.zero(1) if rng.getrandbits(1) else 0)
        elif k < 0.85:                                  # one shifted under the other
            b = with_exponent(f, pick(f, rng), field(f, a) + rng.randrange(-f.fw - 4, f.fw + 5))
        else:
            b = with_exponent(f, pick(f, rng), f.top - 1 - rng.randrange(3))
            a = with_exponent(f, a, f.top - 1 - rng.randrange(3))
        return [a, b, 0]
    if name == "multiply":
        b = pick(f, rng)
        if k < 0.25:                                    # product at the bottom of the format
            b = with_exponent(f, b, f.bias + rng.randrange(f.emin - f.fw - 3, f.emin + 4) - (field(f, a) - f.bias))
        elif k < 0.50:                                  # product at the top
            b = with_exponent(f, b, f.bias + f.emax + rng.randrange(-2, 3) - (field(f, a) - f.bias))
        return [a, b, 0]
    if name == "dividebyp2":                            # the divisor is a power of two
        if k < 0.40:
            b = rng.randrange(1, f.top) << f.fw
        elif k < 0.55:
            b = 1 << rng.randrange(f.fw)                # a denormal one
        else:                                           # quotient at the bottom of the format: ties
            b = min(f.top - 1, max(1, field(f, a) - rng.randrange(f.emin - f.fw - 3, f.emin + 4))) << f.fw
        return [a, f.zero(rng.getrandbits(1)) | b, 0]
    if name == "scalb":
        e = field(f, a) - f.bias
        if k < 0.35:
            n = rng.randrange(-2 * f.fw - 8, 2 * f.fw + 9)
        elif k < 0.60:                                  # result at the bottom of the format
            n = rng.randrange(f.emin - f.fw - 3, f.emin + 4) - e
        elif k < 0.80:                                  # at the top
            n = f.emax + rng.randrange(-2, 3) - e
        else:
            n = rng.choice([-1, 1]) * rng.choice([1000, 70000, 1 << 20, 1 << 30])
        return [a, 0, 0, n]
    if name == "divide":
        b = pick(f, rng)
        if k < 0.20:                                    # quotients that come out exact
            m, d = rng.randrange(1, 1 << min(f.fw, 12)), rng.randrange(1, 64)
            e = Fraction(2) ** rng.randrange(-f.fw, f.fw)
            a = rounded(f, rng.getrandbits(1), m * d * e, NEAREST)
            b = rounded(f, rng.getrandbits(1), Fraction(d), NEAREST)
        elif k < 0.40:                                  # quotient at the bottom of the format
            b = with_exponent(f, b, field(f, a) - rng.randrange(f.emin - f.fw - 3, f.emin + 4))
        elif k < 0.55:                                  # quotient at the top
            b = with_exponent(f, b, field(f, a) - f.emax + rng.randrange(-2, 3))
        elif k < 0.70:                                  # a power of two that shifts a small number lower: ties
            a = with_exponent(f, a, rng.randrange(1, min(f.top, f.fw + 4)))
            b = f.zero(rng.getrandbits(1)) | ((f.bias + rng.randrange(1, f.fw + 4)) << f.fw)
        return [a, b, 0]
    if name in ("sqrt", "reciprocal"):
        a = pick(f, rng, positive=(name == "sqrt" and k < 0.95))
        if k < 0.15:                                    # squares and powers of two
            n = rng.randrange(1, 1 << (f.fw // 2 + 1))
            a = rounded(f, 0, Fraction(n * n if name == "sqrt" else 1) * Fraction(2) ** (2 * rng.randrange(-20, 20)),
                        NEAREST)
        return [a, 0, 0]
    if name == "mac":
        b, c = pick(f, rng), pick(f, rng)
        if k < 0.30:                                    # the product and c cancel, or nearly
            p = multiply(f, decode(f, a), decode(f, b), NEAREST)
            if p != NAN:
                c = near(f, p, rng) ^ f.zero(1)
        elif k < 0.45:                                  # c shifted under the product or above it
            c = with_exponent(f, c, field(f, a) + field(f, b) - f.bias + rng.randrange(-2 * f.fw - 6, f.fw + 6))
        elif k < 0.55:
            c = f.zero(rng.getrandbits(1))
        elif k < 0.65:
            b = f.zero(rng.getrandbits(1))
        return [a, b, c]
    if name == "resize":
        g = Fmt(p1, p2)                                 # a number of the target, widened, with low bits added
        if k < 0.60 and f.fw > g.fw and f.ew >= g.ew:
            x = decode(g, pick(g, rng))
            if x != NAN and x[1] != "inf" and x[1] != 0:
                unit = Fraction(2) ** (max(floor_log2(x[1]), g.emin) - g.fw)
                low = rng.choice([0, Fraction(1, 2), Fraction(1, 2) + Fraction(1, 1 << (f.fw - g.fw - 1)),
                                  Fraction(1, 2) - Fraction(1, 1 << (f.fw - g.fw - 1)), Fraction(1, 4),
                                  Fraction(rng.getrandbits(f.fw - g.fw), 1 << (f.fw - g.fw))])
                a = rounded(f, x[0], x[1] + low * unit, ZERO)
        elif k < 0.75:                                  # around the target's smallest and largest numbers
            e = rng.choice([g.emin - g.fw, g.emin, g.emax]) + rng.randrange(-3, 4)
            a = with_exponent(f, a, e + f.bias)
        return [a, 0, 0]
    if name in FROM_INT:
        n = rng.getrandbits(rng.randrange(1, p1 + 1))
        if k < 0.3:
            n |= (1 << rng.randrange(1, p1 + 1)) - 1
        n &= (1 << p1) - 1
        return [0 if n == 1 << (p1 - 1) else n, 0, 0]   # the most negative number has no negative
    # to_signed, to_unsigned, to_integer: an integer and a part of one
    size = 30 if name == "to_integer" else p1
    whole = rng.getrandbits(rng.randrange(0, min(size, f.fw + 2)))
    part = rng.choice([0, Fraction(1, 2), Fraction(1, 4), Fraction(3, 4), Fraction(1, 8), Fraction(7, 8),
                       Fraction(rng.getrandbits(8), 256)])
    v = whole + part
    if k < 0.25:                                        # one unit of the last place beside it
        a = near(f, rounded(f, rng.getrandbits(1), v, NEAREST), rng) if v else pick(f, rng)
    elif k < 0.85:
        a = rounded(f, rng.getrandbits(1), v, NEAREST) if v else f.zero(rng.getrandbits(1))
    if name == "to_integer" and field(f, a) > f.bias + 29:
        a = with_exponent(f, a, f.bias + 29)            # an INTEGER holds less than 2**31
    return [a, 0, 0]


def targets(name, f):
    """(p1, p2) for the operations that take them."""
    if name == "resize":
        return [g for g in [(5, 10), (8, 23), (11, 52), (15, 112), (4, 3)] if g != (f.ew, f.fw)]
    if name in ("to_signed", "to_unsigned"):
        return [(8, 0), (32, 0), (64, 0)]
    if name == "to_float":
        return [(32, 0), (64, 0)]
    if name == "to_float_integer":
        return [(32, 0)]
    return [(0, 0)]


def line(op, st, f, p1, p2, ops, guard=3, denormalize=1):
    widths = [p1] if OPS[op] in FROM_INT else [f.w] * (3 if op < 7 or op > 12 else 1)
    return "%d %d %d %d %d %d %d %d %s" % (op, st, f.ew, f.fw, guard, denormalize, p1, p2,
                                           " ".join(format(x, "0%db" % w) for x, w in zip(ops, widths)))


def gen(seed, n, formats, names, guard=3, denormalize=1):
    rng = random.Random(seed)
    for ew, fw in formats:
        f = Fmt(ew, fw)
        for name in names:
            for p1, p2 in targets(name, f):
                for i in range(n * 4):
                    ops = operands(name, f, p1, p2, rng)
                    if name == "scalb":
                        p1 = ops.pop()
                    print(line(OPS.index(name), i & 3, f, p1, p2, ops, guard, denormalize))


def everything(ew, fw, names):
    f = Fmt(ew, fw)
    values = range(1 << f.w)
    for name in names:
        op = OPS.index(name)
        for p1, p2 in targets(name, f):
            if name in FROM_INT:
                continue
            for st in range(4):
                for a in values:
                    if name in ("add", "subtract", "multiply", "divide"):
                        for b in values:
                            print(line(op, st, f, p1, p2, [a, b, 0]))
                    elif name == "dividebyp2":
                        for b in values:
                            m = b & ((1 << (f.w - 1)) - 1)
                            if m and m & (m - 1) == 0 or (m and m & ((1 << f.fw) - 1) == 0 and m >> f.fw != f.top):
                                print(line(op, st, f, p1, p2, [a, b, 0]))
                    elif name == "scalb":
                        span = (1 << (f.ew + 1)) + f.fw + 6
                        for n in range(-span, span + 1):
                            print(line(op, st, f, n, p2, [a, 0, 0]))
                    elif name == "mac":
                        for b in values:
                            for c in values:
                                print(line(op, st, f, p1, p2, [a, b, c]))
                    else:
                        print(line(op, st, f, p1, p2, [a, 0, 0]))


# ---- the simulator and the comparison -------------------------------------------------------------------

def run(vec, out, cmd, piece=50000):
    """Runs the testbench over the vectors, a piece at a time. A line that stops the simulator inside the package
    is recorded as STOP, and the testbench is started again behind it: {skip} in CMD is the number of lines of
    the piece to pass over."""
    part, cut = out + ".part", out + ".piece"
    stops = total = 0
    with open(vec) as source, open(out, "w") as result:
        while True:
            lines = list(itertools.islice(source, piece))
            if not lines:
                break
            with open(cut, "w") as fh:
                fh.writelines(lines)
            start = 0
            while start < len(lines):
                open(part, "w").close()
                subprocess.run([c.replace("{vec}", cut).replace("{out}", part).replace("{skip}", str(start))
                                for c in cmd], capture_output=True, text=True)
                with open(part) as fh:
                    done = fh.read().split("\n")
                if done and done[-1] == "":
                    done.pop()
                for d in done:
                    result.write(d + "\n")
                start += len(done)
                if start < len(lines):
                    result.write("STOP\n")
                    stops += 1
                    start += 1
            total += len(lines)
    for name in (part, cut):
        if os.path.exists(name):
            os.remove(name)
    print("%d lines, %d stopped the simulator" % (total, stops))


def is_nan(f, bits):
    return (bits >> f.fw) & f.top == f.top and bits & ((1 << f.fw) - 1) != 0


def show(value, width):
    return "nan" if value == NAN else "%0*x" % ((width + 3) // 4, value)


def check(vec, out):
    total, bad, stop, shown = {}, {}, {}, {}
    for v, r in zip(open(vec), open(out)):
        t = v.split()
        op, st, ew, fw, guard, dn, p1, p2 = [int(x) for x in t[:8]]
        ops = [int(x, 2) for x in t[8:]]
        f = Fmt(ew, fw)
        name = OPS[op]
        want = expected(op, st, f, p1, p2, ops)
        if want is None:
            continue
        label = name + (" to %d,%d" % (p1, p2) if name == "resize" else " %d" % p1 if p1 and name != "scalb" else "")
        key = ("%d,%d" % (ew, fw), label)
        total[key + (st,)] = total.get(key + (st,), 0) + 1
        r = r.strip()
        g = Fmt(p1, p2) if name == "resize" else f
        width = g.w if name not in TO_INT else 32 if name == "to_integer" else p1
        if r == "STOP":
            stop[key + (st,)] = stop.get(key + (st,), 0) + 1
            got = "stops the simulator"
        else:
            got = int(r) if name == "to_integer" else int(r.replace("X", "1").replace("U", "1"), 2)
            if name == "to_integer":
                if got == want:
                    continue
                got, want = "%d" % got, "%d" % want
            else:
                if got == want or (want == NAN and is_nan(g, got)):
                    continue
                got = "returns " + show(got, width)
            bad[key + (st,)] = bad.get(key + (st,), 0) + 1
        if shown.get(key + (st,), 0) < 2:
            shown[key + (st,)] = shown.get(key + (st,), 0) + 1
            print("  %s %s %s (%s)  %s, exact %s" % (key[0], label, STYLE[st],
                                                    " ".join(show(x, p1 if name in FROM_INT else f.w) for x in
                                                             ops[:3 if name == "mac" else
                                                                 2 if op < 4 or name == "dividebyp2" else 1])
                                                    + (", %d" % p1 if name == "scalb" else ""),
                                                    got, want if isinstance(want, str) else show(want, width)))
    print()
    print("%-8s %-21s %s" % ("format", "operation", "".join("%-24s" % s for s in STYLE)))
    for key in dict.fromkeys(k[:2] for k in total):
        cells = []
        for st in range(4):
            k = key + (st,)
            cell = "%d of %d" % (bad.get(k, 0), total.get(k, 0))
            if stop.get(k):
                cell += ", %d stop" % stop[k]
            cells.append("%-24s" % cell)
        print("%-8s %-21s %s" % (key[0], key[1], "".join(cells)))
    print()
    print("%d wrong and %d stops in %d operations" % (sum(bad.values()), sum(stop.values()), sum(total.values())))


def pairs(args):
    return [tuple(int(x) for x in a.split(",")) for a in args]


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        rest = [a for a in sys.argv[4:] if "=" not in a]
        opt = dict(a.split("=") for a in sys.argv[4:] if "=" in a)      # guard=3 denormalize=1 are the package's
        gen(int(sys.argv[2]), int(sys.argv[3]), pairs([a for a in rest if "," in a]),
            [a for a in rest if "," not in a] or OPS, int(opt.get("guard", 3)), int(opt.get("denormalize", 1)))
    elif sys.argv[1] == "all":
        ew, fw = pairs([sys.argv[2]])[0]
        everything(ew, fw, sys.argv[3:] or OPS)
    elif sys.argv[1] == "run":
        run(sys.argv[2], sys.argv[3], sys.argv[sys.argv.index("--") + 1:])
    else:
        check(sys.argv[2], sys.argv[3])
