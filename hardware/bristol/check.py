"""Checks the circuits of this folder against the published Bristol Fashion circuits and against rules.py.

usage: python3 check.py DIR [VECTORS] [SEED] [NAMES]   DIR holds the published files: FP-add.txt, mult64.txt, ... from
                                                    https://nigelsmart.github.io/MPC-Circuits/ and ModAdd512.txt,
                                                    LSSS_to_GC.txt from SCALE-MAMBA (Circuits/Bristol)
       python3 check.py bench DIR OUT               writes OUT/NAME.published.bench and OUT/NAME.here.bench
                                                    for an equivalence proof with ABC:  cec A.bench B.bench

For each function it runs both circuits on the same operands and counts the operands on which the circuit here
differs from the published one and from the rule. VECTORS operands per function, 100000 by default, and a tenth
of that for the two 512-bit circuits. The operands are the special values in every combination, random patterns,
and operands aimed at rounding ties, alignment, cancellation, overflow, underflow and subnormal results.
The exit status is 1 when any count is not zero. It needs Python only.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import rules

M64 = (1 << 64) - 1
BIAS = 1023


# ---- Bristol Fashion ---------------------------------------------------------------------------
class Circuit:
    """A wire value is an integer whose bit t is the value of the wire on operand vector t."""

    def __init__(self, path):
        with open(path) as f:
            lines = [t.split() for t in f.read().split("\n") if t.strip()]
        self.nwires = int(lines[0][1])
        self.in_sizes = [int(x) for x in lines[1][1:1 + int(lines[1][0])]]
        self.out_sizes = [int(x) for x in lines[2][1:1 + int(lines[2][0])]]
        self.gates = []
        for t in lines[3:]:
            ni, no = int(t[0]), int(t[1])
            self.gates.append((t[-1], tuple(int(x) for x in t[2:2 + ni]), tuple(int(x) for x in t[2 + ni:2 + ni + no])))
        if len(self.gates) != int(lines[0][0]):
            raise ValueError(path + ": gate count does not match the header")

    def count(self):
        """(AND gates, AND depth)"""
        depth = [0] * self.nwires
        ands = 0
        for op, ins, outs in self.gates:
            if op == "AND":
                ands += 1
                depth[outs[0]] = max(depth[ins[0]], depth[ins[1]]) + 1
            elif op == "XOR":
                depth[outs[0]] = max(depth[ins[0]], depth[ins[1]])
            elif op in ("INV", "EQW"):
                depth[outs[0]] = depth[ins[0]]
            elif op == "MAND":
                for k in range(len(outs)):
                    ands += 1
                    depth[outs[k]] = max(depth[ins[2 * k]], depth[ins[2 * k + 1]]) + 1
        return ands, max(depth[self.nwires - sum(self.out_sizes):])

    def run(self, inputs, mask):
        w = [0] * self.nwires
        w[:len(inputs)] = inputs
        for op, ins, outs in self.gates:
            if op == "XOR":
                w[outs[0]] = w[ins[0]] ^ w[ins[1]]
            elif op == "AND":
                w[outs[0]] = w[ins[0]] & w[ins[1]]
            elif op == "INV":
                w[outs[0]] = w[ins[0]] ^ mask
            elif op == "EQW":
                w[outs[0]] = w[ins[0]]
            elif op == "EQ":
                w[outs[0]] = mask if ins[0] else 0
            elif op == "MAND":
                for k in range(len(outs)):
                    w[outs[k]] = w[ins[2 * k]] & w[ins[2 * k + 1]]
            else:
                raise ValueError("gate " + op)
        return w[self.nwires - sum(self.out_sizes):]


def pack(values, width):
    wires = []
    for b in range(width):
        x = 0
        for t, v in enumerate(values):
            if (v >> b) & 1:
                x |= 1 << t
        wires.append(x)
    return wires


def unpack(wires, count):
    out = [0] * count
    for b, x in enumerate(wires):
        while x:
            low = x & -x
            out[low.bit_length() - 1] |= 1 << b
            x ^= low
    return out


# ---- operands ----------------------------------------------------------------------------------
SPECIALS = [
    0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001, 0x0000000000000002,
    0x000fffffffffffff, 0x800fffffffffffff, 0x0010000000000000, 0x8010000000000000, 0x0010000000000001,
    0x001fffffffffffff, 0x0008000000000000, 0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001,
    0x3fefffffffffffff, 0x4000000000000000, 0x3fe0000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
    0x7fe0000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
    0x7ff0000000000001, 0xfff0000000000001, 0x7ff7ffffffffffff, 0x7fffffffffffffff, 0xffffffffffffffff,
    0x7ff8000000000001, 0xfff8000000000005, 0x7ff4000000000000, 0x4340000000000000, 0x4330000000000000,
    0x433fffffffffffff, 0x43e0000000000000, 0xc3e0000000000000, 0x43dfffffffffffff, 0xc3e0000000000001,
    0x3fd0000000000000, 0x3ff8000000000000, 0x4004000000000000, 0xc004000000000000, 0x3fe0000000000001,
    0x3fdfffffffffffff, 0x4008000000000000, 0x4022000000000000, 0x1e60000000000000, 0x0020000000000000,
]
FRAC = (1 << 52) - 1


def mantissa(rng):
    k = rng.randrange(12)
    if k == 0:
        return 0
    if k == 1:
        return FRAC
    if k == 2:
        return 1 << rng.randrange(52)
    if k == 3:
        return FRAC ^ (1 << rng.randrange(52))
    if k == 4:
        return rng.getrandbits(rng.randrange(1, 53))
    if k == 5:
        s = rng.randrange(1, 52)
        return (rng.getrandbits(52) >> s) << s
    if k == 6:
        return FRAC >> rng.randrange(52)
    if k == 7:
        s = rng.randrange(52)
        return (FRAC >> s) << s
    if k == 8:
        return rng.getrandbits(52) & rng.getrandbits(52) & rng.getrandbits(52)
    return rng.getrandbits(52)


def exponent(rng):
    k = rng.randrange(10)
    if k == 0:
        return rng.choice([0, 0, 1, 2, 3])
    if k == 1:
        return rng.choice([0x7ff, 0x7fe, 0x7fd, 0x7fc])
    if k == 2:
        return BIAS + rng.randrange(-3, 4)
    if k == 3:
        return BIAS + rng.randrange(50, 66)
    if k == 4:
        return BIAS - rng.randrange(50, 66)
    if k == 5:
        return rng.randrange(1, 60)
    return rng.randrange(0x800)


def clamp(e):
    return max(0, min(0x7ff, e))


def one(rng):
    k = rng.randrange(20)
    if k == 0:
        return rng.choice(SPECIALS)
    if k == 1:
        return rng.getrandbits(64)
    return (rng.getrandbits(1) << 63) | (exponent(rng) << 52) | mantissa(rng)


def near(rng, a):
    s, e, m = a >> 63, (a >> 52) & 0x7ff, a & FRAC
    k = rng.randrange(8)
    if k == 0:
        return (rng.getrandbits(1) << 63) | (e << 52) | ((m + rng.randrange(-3, 4)) & FRAC)
    if k == 1:
        return ((s ^ 1) << 63) | (clamp(e + rng.randrange(-1, 2)) << 52) | ((m + rng.randrange(-2, 3)) & FRAC)
    if k == 2:
        return (rng.getrandbits(1) << 63) | (clamp(e + rng.randrange(-2, 3)) << 52) | mantissa(rng)
    if k == 3:
        return (rng.getrandbits(1) << 63) | (clamp(e - rng.randrange(50, 58)) << 52) | mantissa(rng)
    if k == 4:
        return (rng.getrandbits(1) << 63) | (clamp(e + rng.randrange(50, 58)) << 52) | mantissa(rng)
    if k == 5:
        return a ^ (rng.getrandbits(1) << 63)
    return one(rng)


def float_pair(rng, name):
    x = one(rng)
    k = rng.randrange(10)
    sign = lambda: rng.getrandbits(1) << 63
    if name in ("FP-add", "FP-eq", "FP-lt"):
        return x, (near(rng, x) if k < 7 else one(rng))
    if name == "FP-mul":
        if k < 3:                                        # exponent sum near the underflow or overflow boundary
            ex = rng.randrange(1, 0x7ff)
            target = rng.choice([BIAS - 54, BIAS - 53, BIAS - 52, BIAS - 51, BIAS - 1, BIAS, BIAS + 1, BIAS + 2,
                                 2 * BIAS + 1022, 2 * BIAS + 1023, 2 * BIAS + 1024, 2 * BIAS + 1025]) + rng.randrange(-2, 3)
            return sign() | (ex << 52) | mantissa(rng), sign() | (clamp(target - ex) << 52) | mantissa(rng)
        if k < 5:                                        # few significant bits each: products with exact ties
            ka = rng.randrange(1, 54)
            kb = max(1, min(53, rng.choice([53, 54, 55, 56]) - ka))
            ma = (rng.getrandbits(ka) | 1 | (1 << (ka - 1))) << (53 - ka)
            mb = (rng.getrandbits(kb) | 1 | (1 << (kb - 1))) << (53 - kb)
            ex, ey = max(1, min(0x7fe, exponent(rng))), max(1, min(0x7fe, exponent(rng)))
            return sign() | (ex << 52) | (ma & FRAC), sign() | (ey << 52) | (mb & FRAC)
        return x, one(rng)
    # FP-div
    if k < 3:                                            # exponent difference near the underflow or overflow boundary
        ey = rng.randrange(1, 0x7ff)
        target = rng.choice([-BIAS - 54, -BIAS - 53, -BIAS - 52, -BIAS - 51, -BIAS - 1, -BIAS, -BIAS + 1, -BIAS + 2,
                             BIAS - 1, BIAS, BIAS + 1, BIAS + 2]) + rng.randrange(-2, 3)
        return sign() | (clamp(target + ey) << 52) | mantissa(rng), sign() | (ey << 52) | mantissa(rng)
    if k < 5:                                            # exact quotients, also landing among the subnormals
        kq = rng.randrange(1, 30)
        ky = rng.randrange(1, 54 - kq)
        q = rng.getrandbits(kq) | 1 | (1 << (kq - 1))
        my = rng.getrandbits(ky) | 1 | (1 << (ky - 1))
        mx = q * my
        mx <<= 53 - mx.bit_length()
        my <<= 53 - my.bit_length()
        ey = rng.randrange(1, 0x7ff)
        ex = max(1, min(0x7fe, ey + rng.choice([0, 1, -1, rng.randrange(-1080, -1010), rng.randrange(-60, 60)])))
        return sign() | (ex << 52) | (mx & FRAC), sign() | (ey << 52) | (my & FRAC)
    return x, (near(rng, x) if k < 7 else one(rng))


def square(rng):
    k = rng.randrange(8)
    if k < 3:                                            # perfect squares and their neighbours
        n = rng.randrange(1, 54)
        r = rng.getrandbits(n) | 1 | (1 << (n - 1))
        sq = r * r
        if sq.bit_length() > 53:
            sq >>= sq.bit_length() - 53
        sq <<= 53 - sq.bit_length()
        x = (rng.randrange(1, 0x7ff) << 52) | (sq & FRAC)
        return (x + rng.choice([0, 0, 1, -1, 2, -2])) & 0x7fffffffffffffff
    if k == 3:
        return rng.getrandbits(52)
    if k == 4:
        return rng.getrandbits(rng.randrange(1, 53))
    x = one(rng)
    return x & 0x7fffffffffffffff if rng.randrange(4) else x


INT_EDGE = [0, 1, 2, 3, 5, M64, M64 - 1, M64 - 4, 1 << 63, (1 << 63) - 1, (1 << 63) + 1, 1 << 32, (1 << 32) - 1, 1 << 62, 3 << 62]


def integer(rng):
    k = rng.randrange(6)
    if k == 0:
        return rng.getrandbits(64)
    if k == 1:
        return rng.getrandbits(rng.randrange(1, 65))
    if k == 2:                                           # more than 53 significant bits, beside a rounding point
        b = rng.randrange(54, 64)
        return (1 << b) | (rng.getrandbits(53) << (b - 53)) | rng.choice([0, 1 << (b - 54), (1 << (b - 54)) + 1, (1 << (b - 54)) - 1])
    if k == 3:
        return (-rng.getrandbits(rng.randrange(1, 64))) & M64
    if k == 4:
        return ((1 << rng.randrange(1, 65)) - 1) ^ (rng.getrandbits(1) * M64)
    return ((1 << rng.randrange(64)) + rng.randrange(-2, 3)) & M64


def int_pair(rng, name):
    k = rng.randrange(8)
    x = integer(rng)
    if k == 0:
        return x, x
    if k == 1:
        return x, rng.choice(INT_EDGE)
    if k == 2 and "divide" in name:                      # an exact multiple, or one off
        y = rng.getrandbits(rng.randrange(1, 33)) or 1
        return (y * rng.getrandbits(rng.randrange(1, 32)) + rng.choice([0, 0, 1, -1])) & M64, y * rng.choice([1, -1]) & M64
    return x, integer(rng)


M512 = (1 << 512) - 1
MODULI = [(1 << 255) - 19, (1 << 127) - 1, (1 << 61) - 1, 97, 3, (1 << 511) + 111, M512, M512 - 2, 1, 2, 0,
          (1 << 511) - 187, (1 << 256) - 189]


def triple(rng):
    """two summands and a modulus of 512 bits: reduced and unreduced summands, sums beside the turning points"""
    k = rng.randrange(9)
    p = rng.choice(MODULI) if k < 5 else rng.getrandbits(rng.randrange(1, 513))
    q = max(p, 1)
    if k == 0:
        a, b = rng.randrange(q), rng.randrange(q)
    elif k == 1:
        a, b = max(p - 1, 0), rng.choice([0, 1, 2, max(p - 1, 0)])
    elif k == 2:
        a, b = rng.getrandbits(512), rng.getrandbits(512)
    elif k == 3:
        a, b = rng.getrandbits(512), 0
    elif k == 4:
        a = rng.randrange(q)
        b = (p - a + rng.choice([-1, 0, 1])) % q if p else 0
    elif k == 5:
        t = rng.choice([p >> 1, p + (p >> 1), p]) + rng.choice([-1, 0, 1])
        a = rng.randrange(max(min(t, M512), 1))
        b = max(0, min(M512, t - a))
    else:
        a, b = rng.getrandbits(rng.randrange(1, 513)), rng.getrandbits(rng.randrange(1, 513))
    return a & M512, b & M512, p & M512


def operands(name, arity, rng, n):
    """n operand tuples, starting with every combination of the special values"""
    out = []
    if arity == 3:
        return [triple(rng) for _ in range(n)]
    if name.startswith("FP-") and name != "FP-i2f":
        out = [(x,) for x in SPECIALS] if arity == 1 else [(x, y) for x in SPECIALS for y in SPECIALS]
    else:
        out = [(x,) for x in INT_EDGE] if arity == 1 else [(x, y) for x in INT_EDGE for y in INT_EDGE]
    while len(out) < n:
        if name == "FP-sqrt":
            out.append((square(rng),))
        elif name == "FP-i2f":
            out.append((integer(rng),))
        elif name.startswith("FP-") and arity == 1:
            out.append((one(rng),))
        elif name.startswith("FP-"):
            out.append(float_pair(rng, name))
        else:
            out.append(int_pair(rng, name))
    return out[:n]


# ---- the check ---------------------------------------------------------------------------------
def check(folder, vectors, seed, only=None):
    failed = False
    for name, (widths, rule) in rules.FUNCTIONS.items():
        if only and name not in only:
            continue
        arity = len(widths)
        here = Circuit(os.path.join(HERE, name + ".txt"))
        pub = Circuit(os.path.join(folder, name + ".txt"))
        assert here.in_sizes == pub.in_sizes == list(widths) and here.out_sizes == pub.out_sizes
        rng = random.Random("%s %d" % (name, seed))
        count = vectors if arity < 3 else max(1, vectors // 10)        # the 512-bit circuits take a tenth
        ops = operands(name, arity, rng, count)
        d_pub = d_rule = 0
        example = None
        step = 16384 if arity < 3 else 2048
        for s in range(0, len(ops), step):
            chunk = ops[s:s + step]
            wires = []
            for k in range(arity):
                wires += pack([o[k] for o in chunk], widths[k])
            mask = (1 << len(chunk)) - 1
            got = unpack(here.run(wires, mask), len(chunk))
            ref = unpack(pub.run(wires, mask), len(chunk))
            for o, g, r in zip(chunk, got, ref):
                if g != r:
                    d_pub += 1
                    example = example or (o, g, r)
                if g != rule(*o):
                    d_rule += 1
        a_here, depth_here = here.count()
        a_pub, depth_pub = pub.count()
        print("%-10s published %6d AND, depth %4d   here %5d AND, depth %4d   %d operands: %d differ from the published circuit, %d from the rule" % (
            name, a_pub, depth_pub, a_here, depth_here, len(ops), d_pub, d_rule))
        if example:
            print("           first: %s -> %x, published %x" % (" ".join("%x" % v for v in example[0]), example[1], example[2]))
        sys.stdout.flush()
        failed = failed or d_pub or d_rule
    return 1 if failed else 0


def to_bench(src, dst):
    c = Circuit(src)
    nin, nout = sum(c.in_sizes), sum(c.out_sizes)
    name = ["i%d" % i if i < nin else "w%d" % i for i in range(c.nwires)]
    lines = ["INPUT(i%d)" % i for i in range(nin)] + ["OUTPUT(o%d)" % k for k in range(nout)]
    for op, ins, outs in c.gates:
        if op in ("AND", "XOR"):
            lines.append("%s = %s(%s, %s)" % (name[outs[0]], op, name[ins[0]], name[ins[1]]))
        elif op == "INV":
            lines.append("%s = NOT(%s)" % (name[outs[0]], name[ins[0]]))
        elif op == "EQW":
            lines.append("%s = BUFF(%s)" % (name[outs[0]], name[ins[0]]))
        elif op == "MAND":
            for k in range(len(outs)):
                lines.append("%s = AND(%s, %s)" % (name[outs[k]], name[ins[2 * k]], name[ins[2 * k + 1]]))
        else:
            raise ValueError("gate " + op)
    lines += ["o%d = BUFF(%s)" % (k, name[c.nwires - nout + k]) for k in range(nout)]
    with open(dst, "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "bench":
        os.makedirs(sys.argv[3], exist_ok=True)
        for fn in rules.FUNCTIONS:
            to_bench(os.path.join(sys.argv[2], fn + ".txt"), os.path.join(sys.argv[3], fn + ".published.bench"))
            to_bench(os.path.join(HERE, fn + ".txt"), os.path.join(sys.argv[3], fn + ".here.bench"))
        sys.exit(0)
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    sys.exit(check(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 100000, int(sys.argv[3]) if len(sys.argv) > 3 else 1,
                   sys.argv[4].split(",") if len(sys.argv) > 4 else None))
