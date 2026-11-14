# The operations of the VHDL fixed-point package in exact arithmetic, with the vectors and the comparison.
#
#   python3 fixed_exact.py gen > vectors.txt        every operand of a set of small index ranges
#   python3 fixed_exact.py check vectors.txt results.txt
#
# A number is a fraction of two integers. A result is (high, low, bits), an integer, or a pair of flags, in
# the form tb_fixed.vhd prints it. None means the package's documentation does not say what comes out.
import sys
from fractions import Fraction

OPS = ["+", "-", "*", "/", "divide", "reciprocal", "rem", "mod", "resize", "to_integer", "scalb", "neg", "abs",
       "compare", "add_carry"]
ROUND, TRUNCATE = 0, 1
SATURATE, WRAP = 0, 1


def value(kind, n, hi, lo):
    w = hi - lo + 1
    if kind and n >> (w - 1):
        n -= 1 << w
    return Fraction(n) * Fraction(2) ** lo


def limits(kind, hi, lo):
    w = hi - lo + 1
    return (-(1 << (w - 1)), (1 << (w - 1)) - 1) if kind else (0, (1 << w) - 1)


def fixed(kind, v, hi, lo):
    """The exact value v in (hi downto lo), or None when it does not fit."""
    n = v / Fraction(2) ** lo
    lo_n, hi_n = limits(kind, hi, lo)
    if n.denominator != 1 or not lo_n <= n <= hi_n:
        return None
    return (hi, lo, int(n) & ((1 << (hi - lo + 1)) - 1))


def units(v, lo, style):
    """v in units of 2**lo: rounded to nearest with ties to even, or cut off toward minus infinity."""
    q = v / Fraction(2) ** lo
    n = q.numerator // q.denominator
    rest = q - n
    if style == ROUND and (2 * rest > 1 or (2 * rest == 1 and n & 1)):
        n += 1
    return n


def fitted(kind, n, hi, lo, ovf):
    lo_n, hi_n = limits(kind, hi, lo)
    w = hi - lo + 1
    if ovf == SATURATE:
        n = max(lo_n, min(hi_n, n))
    return (hi, lo, n & ((1 << w) - 1))


def expected(op, kind, lh, ll, rh, rl, p1, p2, style, ovf, a, b):
    name = OPS[op]
    x, y = value(kind, a, lh, ll), value(kind, b, rh, rl)
    if name == "+":
        return fixed(kind, x + y, max(lh, rh) + 1, min(ll, rl))
    if name == "-":
        return fixed(kind, x - y, max(lh, rh) + 1, min(ll, rl))
    if name == "*":
        return fixed(kind, x * y, lh + rh + 1, ll + rl)
    if name in ("/", "divide"):
        if y == 0:
            return None
        hi, lo = (lh - rl + 1, ll - rh) if kind else (lh - rl, ll - rh - 1)
        st = ROUND if name == "/" else style
        if name == "divide" and p1 == 0:
            st = TRUNCATE                               # no guard bits: nothing to round with
        return fitted(kind, units(x / y, lo, st), hi, lo, WRAP)
    if name == "reciprocal":
        if x == 0:
            return None
        hi, lo = (-ll + 1, -lh) if kind else (-ll, -lh - 1)
        st = TRUNCATE if p1 == 0 else style
        return fitted(kind, units(1 / x, lo, st), hi, lo, WRAP)
    if name in ("rem", "mod"):
        if y == 0:
            return None
        q = x / y
        whole = q.numerator // q.denominator            # floor
        if name == "rem" and q < 0 and q.denominator != 1:
            whole += 1                                  # toward zero
        r = x - y * whole
        hi = rh if (name == "mod" and kind) else min(lh, rh)
        return fixed(kind, r, hi, min(ll, rl))
    if name == "resize":
        return fitted(kind, units(x, p2, style), p1, p2, ovf)
    if name == "to_integer":
        return units(x, 0, style)
    if name == "scalb":
        return (lh + p1, ll + p1, a)
    if name == "neg":
        return fixed(kind, -x, lh + 1, ll)
    if name == "abs":
        return fixed(kind, abs(x), lh + 1, ll)
    if name == "compare":
        return (int(x < y), int(x == y))
    hi, lo = max(lh, rh), min(ll, rl)                   # add_carry
    n = (x + y) / Fraction(2) ** lo + p1
    w = hi - lo + 1
    return (hi, lo, int(n) & ((1 << w) - 1), int(n) >> w)


RANGES = [((3, -3), (3, -3)), ((2, -1), (1, -3)), ((0, -4), (3, 0)), ((-1, -4), (2, -2)), ((4, 1), (1, -2)),
          ((2, -2), (4, -1))]
TARGETS = [(0, 0), (1, -1), (-1, -2), (2, 1), (4, -4)]  # offsets added to the operand's own range for resize


def gen():
    for kind in (0, 1):
        for (lh, ll), (rh, rl) in RANGES:
            wa, wb = lh - ll + 1, rh - rl + 1

            def out(op, p1, p2, style, ovf, a, b):
                print("%d %d %d %d %d %d %d %d %d %d %s %s" % (op, kind, lh, ll, rh, rl, p1, p2, style, ovf,
                                                         format(a, "0%db" % wa), format(b, "0%db" % wb)))
            for a in range(1 << wa):
                for b in range(1 << wb):
                    for name in ("+", "-", "*", "/", "rem", "mod", "compare"):
                        out(OPS.index(name), 0, 0, 0, 0, a, b)
                    for guard in (0, 1, 2, 3, 4):
                        for style in (ROUND, TRUNCATE):
                            out(OPS.index("divide"), guard, 0, style, 0, a, b)
                    if not kind:
                        for carry in (0, 1):
                            out(OPS.index("add_carry"), carry, 0, 0, 0, a, b)
                for style in (ROUND, TRUNCATE):
                    for guard in (0, 3):
                        out(OPS.index("reciprocal"), guard, 0, style, 0, a, 0)
                    out(OPS.index("to_integer"), 0, 0, style, 0, a, 0)
                    for dh, dl in TARGETS:
                        for dh2 in (0, -1, -2, 1):
                            p1, p2 = lh + dh2, ll - dl if dl <= 0 else ll + dl
                            if p1 >= p2:
                                for ovf in (SATURATE, WRAP):
                                    out(OPS.index("resize"), p1, p2, style, ovf, a, 0)
                for n in (-3, 0, 2):
                    out(OPS.index("scalb"), n, 0, 0, 0, a, 0)
                if kind:
                    out(OPS.index("neg"), 0, 0, 0, 0, a, 0)
                    out(OPS.index("abs"), 0, 0, 0, 0, a, 0)


def parse(result):
    t = result.split()
    if not t:
        return "nothing"
    if t[0] == "H":
        r = (int(t[1]), int(t[2]), int(t[3].replace("X", "1").replace("U", "1"), 2) if len(t) > 3 else 0)
        return r + (int(t[4]),) if len(t) > 4 else r
    if t[0] == "I":
        return int(t[1])
    if t[0] == "C":
        return (int(t[1]), int(t[2]))
    return result.strip()


def show(kind, r):
    if isinstance(r, tuple) and len(r) >= 3:
        text = "%s (%d downto %d)" % (value(kind, r[2], r[0], r[1]), r[0], r[1])
        return text + (" carry %d" % r[3] if len(r) > 3 else "")
    return str(r)


def check(vec, out):
    total, bad, shown = {}, {}, {}
    for v, r in zip(open(vec), open(out)):
        t = v.split()
        op, kind, lh, ll, rh, rl, p1, p2, style, ovf = [int(x) for x in t[:10]]
        a, b = int(t[10], 2), int(t[11], 2)
        want = expected(op, kind, lh, ll, rh, rl, p1, p2, style, ovf, a, b)
        if want is None:
            continue
        name = OPS[op]
        label = name
        if name in ("divide", "reciprocal"):
            label += " %s, %d guard" % ("round" if style == ROUND else "truncate", p1)
        elif name in ("resize", "to_integer"):
            label += " " + ("round" if style == ROUND else "truncate")
            if name == "resize":
                label += ", " + ("saturate" if ovf == SATURATE else "wrap")
        key = ("sfixed" if kind else "ufixed", label)
        total[key] = total.get(key, 0) + 1
        got = parse(r)
        if got == want:
            continue
        bad[key] = bad.get(key, 0) + 1
        if shown.get(key, 0) < 2:
            shown[key] = shown.get(key, 0) + 1
            x, y = value(kind, a, lh, ll), value(kind, b, rh, rl)
            extra = " to (%d downto %d)" % (p1, p2) if name == "resize" else " by %d" % p1 if name == "scalb" else ""
            print("  %s %s  %s (%d downto %d), %s (%d downto %d)%s  returns %s, exact %s" % (
                key[0], label, x, lh, ll, y, rh, rl, extra, show(kind, got), show(kind, want)))
    print()
    for key in total:
        print("%-7s %-34s %8d of %d" % (key[0], key[1], bad.get(key, 0), total[key]))
    print()
    print("%d wrong in %d operations" % (sum(bad.values()), sum(total.values())))


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen()
    else:
        check(sys.argv[2], sys.argv[3])
