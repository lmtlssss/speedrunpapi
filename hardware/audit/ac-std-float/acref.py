# Exact reference for ac_std_float<W,E>: the operation done on fractions of integers and rounded once.
# usage: python3 acref.py check OP W.E ROUNDING RESULTS.txt [examples]
#   OP add sub mult div sqrt fma; ROUNDING conv zero inf odd, as actb.cpp names them
#   RESULTS.txt is actb's output: one hex result per operand tuple, in actb's order.
# Rounding: conv is to nearest with ties to even, zero truncates, inf is to nearest with ties away from zero,
# odd is to nearest with ties to odd. Overflow goes to infinity except under truncation, where IEEE 754 gives
# the largest finite number. A NaN result is compared as a NaN, whatever its payload.
import sys
from fractions import Fraction
from math import isqrt


class Fmt:
    def __init__(s, w, e):
        s.w, s.e, s.m = w, e, w - e - 1
        s.bias = (1 << (e - 1)) - 1
        s.emin, s.emax = 1 - s.bias, s.bias
        s.emask = (1 << e) - 1

    def unpack(s, b):
        sign = b >> (s.w - 1)
        e = (b >> s.m) & s.emask
        f = b & ((1 << s.m) - 1)
        if e == s.emask:
            return ("inf" if f == 0 else "nan"), sign, None
        if e == 0:
            return ("zero" if f == 0 else "fin"), sign, Fraction(f) * Fraction(2) ** (s.emin - s.m)
        return "fin", sign, Fraction((1 << s.m) + f) * Fraction(2) ** (e - s.bias - s.m)

    def inf(s, sign):
        return (sign << (s.w - 1)) | (s.emask << s.m)

    def zero(s, sign):
        return sign << (s.w - 1)

    def is_nan(s, b):
        return ((b >> s.m) & s.emask) == s.emask and (b & ((1 << s.m) - 1)) != 0

    def round(s, sign, mag, mode):
        """the bits of the positive fraction mag rounded in the given mode, with the sign"""
        n, d = mag.numerator, mag.denominator
        e = n.bit_length() - d.bit_length()
        if (n << max(0, -e)) < (d << max(0, e)):
            e -= 1
        q = max(e, s.emin) - s.m
        num, den = (n, d << q) if q >= 0 else (n << -q, d)
        k, r = divmod(num, den)
        if mode == "conv":
            inc = 2 * r > den or (2 * r == den and (k & 1) == 1)
        elif mode == "zero":
            inc = False
        elif mode == "inf":
            inc = 2 * r >= den
        else:
            inc = 2 * r > den or (2 * r == den and (k & 1) == 0)
        k += int(inc)
        if k >> (s.m + 1):
            k >>= 1
            q += 1
        if k >> s.m:
            ex = q + s.m
            if ex > s.emax:
                if mode == "zero":
                    return (sign << (s.w - 1)) | ((s.emask - 1) << s.m) | ((1 << s.m) - 1)
                return s.inf(sign)
            return (sign << (s.w - 1)) | ((ex + s.bias) << s.m) | (k - (1 << s.m))
        return (sign << (s.w - 1)) | k


NAN = "nan"


def to_integral(f, op, a):
    """ceil, floor, trunc and round as C and IEEE 754 define them: the sign is kept when the result is zero"""
    ka, sa, ma = f.unpack(a)
    if ka == "nan":
        return NAN
    if ka in ("inf", "zero"):
        return a
    n, r = divmod(ma.numerator, ma.denominator)
    frac = r != 0
    if op == "ceil":
        k = n if sa else n + int(frac)
    elif op == "floor":
        k = n + int(frac) if sa else n
    elif op == "trunc":
        k = n
    else:
        k = n + int(2 * r >= ma.denominator)
    if k == 0:
        return f.zero(sa)
    # k is an integer and fits exactly, except in a format so small that its largest number has a fraction
    # (8.3: 15.5); there the integer above it overflows to infinity
    return f.round(sa, Fraction(k), "conv")


def relation(f, op, a, b):
    ka, sa, ma = f.unpack(a)
    kb, sb, mb = f.unpack(b)
    if ka == "nan" or kb == "nan":
        return int(op == "ne")
    big = Fraction(1 << 4000)
    x = (-1 if sa else 1) * (big if ka == "inf" else ma)
    y = (-1 if sb else 1) * (big if kb == "inf" else mb)
    return int({"lt": x < y, "le": x <= y, "gt": x > y, "ge": x >= y, "eq": x == y, "ne": x != y}[op])


UNARY = ("sqrt", "ceil", "floor", "trunc", "round")
RELATIONS = ("lt", "le", "gt", "ge", "eq", "ne")


def compute(f, op, a, b=0, c=0, mode="conv"):
    if op in ("ceil", "floor", "trunc", "round"):
        return to_integral(f, op, a)
    if op in RELATIONS:
        return relation(f, op, a, b)
    ka, sa, ma = f.unpack(a)
    if op == "sqrt":
        if ka == "nan":
            return NAN
        if ka == "zero":
            return f.zero(sa)
        if sa:
            return NAN
        if ka == "inf":
            return f.inf(0)
        num, den = ma.numerator, ma.denominator
        k = den.bit_length() - 1
        if k & 1:
            num, k = num << 1, k + 1
        extra = 2 * f.m + 12
        num <<= 2 * extra
        root = isqrt(num)
        half = k // 2 + extra
        mag = Fraction(root, 1 << half) if root * root == num else Fraction(2 * root + 1, 1 << (half + 1))
        return f.round(0, mag, mode)
    kb, sb, mb = f.unpack(b)
    if op == "fma":
        kc, sc, mc = f.unpack(c)
        if "nan" in (ka, kb, kc):
            return NAN
        sp = sa ^ sb
        if (ka == "inf" and kb == "zero") or (ka == "zero" and kb == "inf"):
            return NAN
        if ka == "inf" or kb == "inf":
            if kc == "inf" and sc != sp:
                return NAN
            return f.inf(sp)
        if kc == "inf":
            return f.inf(sc)
        p = ma * mb
        v = (-p if sp else p) + (-mc if sc else mc)
        if v == 0:
            return f.zero(sp if (p == 0 and mc == 0 and sp == sc) else 0)
        return f.round(int(v < 0), abs(v), mode)
    if "nan" in (ka, kb):
        return NAN
    if op in ("add", "sub"):
        if op == "sub":
            sb ^= 1
        if ka == "inf" or kb == "inf":
            if ka == "inf" and kb == "inf" and sa != sb:
                return NAN
            return f.inf(sa if ka == "inf" else sb)
        v = (-ma if sa else ma) + (-mb if sb else mb)
        if v == 0:
            return f.zero(sa if (ka == "zero" and kb == "zero" and sa == sb) else 0)
        return f.round(int(v < 0), abs(v), mode)
    s = sa ^ sb
    if op == "mult":
        if ka == "inf" or kb == "inf":
            return NAN if "zero" in (ka, kb) else f.inf(s)
        if ka == "zero" or kb == "zero":
            return f.zero(s)
        return f.round(s, ma * mb, mode)
    # div
    if ka == "inf":
        return NAN if kb == "inf" else f.inf(s)
    if kb == "inf":
        return f.zero(s)
    if kb == "zero":
        return NAN if ka == "zero" else f.inf(s)
    if ka == "zero":
        return f.zero(s)
    return f.round(s, ma / mb, mode)


def operands(f, op):
    n = 1 << f.w
    if op in UNARY:
        for a in range(n):
            yield (a,)
    elif op == "fma":
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    yield (a, b, c)
    else:
        for a in range(n):
            for b in range(n):
                yield (a, b)


def describe(f, b):
    k, s, m = f.unpack(b)
    if k == "nan":
        return "nan"
    if k == "inf":
        return "-inf" if s else "+inf"
    return ("-" if s else "") + str(m)


def check(op, fmt, mode, path, examples):
    w, e = (int(x) for x in fmt.split("."))
    f = Fmt(w, e)
    total = wrong = nanwrong = 0
    kinds = {}
    shown = 0
    with open(path) as res:
        for ops in operands(f, op):
            line = res.readline()
            if not line:
                print("results end after %d" % total)
                break
            got = int(line, 16)
            want = compute(f, op, *ops, mode=mode)
            total += 1
            if op in RELATIONS:
                if got != want:
                    wrong += 1
                    kinds["relation"] = kinds.get("relation", 0) + 1
                    if shown < examples:
                        shown += 1
                        print("  %s %s: %s -> %d, exact %d" % (op, fmt, " ".join("%0*x (%s)" % ((f.w + 3) // 4, x, describe(f, x)) for x in ops), got, want))
                continue
            if want == NAN:
                ok = f.is_nan(got)
            else:
                ok = got == want
            if not ok:
                wrong += 1
                if want == NAN or f.is_nan(got):
                    nanwrong += 1
                    kind = "nan"
                elif (got ^ want) == 1 << (f.w - 1):
                    kind = "sign"
                elif abs((got & ~(1 << (f.w - 1))) - (want & ~(1 << (f.w - 1)))) == 1 and (got >> (f.w - 1)) == (want >> (f.w - 1)):
                    kind = "one unit"
                else:
                    kind = "other"
                kinds[kind] = kinds.get(kind, 0) + 1
                if shown < examples:
                    shown += 1
                    print("  %s %s %s: %s -> %0*x (%s), exact %s" % (
                        op, fmt, mode, " ".join("%0*x (%s)" % ((f.w + 3) // 4, x, describe(f, x)) for x in ops),
                        (f.w + 3) // 4, got, describe(f, got),
                        "nan" if want == NAN else "%0*x (%s)" % ((f.w + 3) // 4, want, describe(f, want))))
    print("%-5s %-5s %-5s %9d operations, %7d wrong %s" % (op, fmt, mode, total, wrong, kinds if kinds else ""))
    return wrong


if __name__ == "__main__":
    check(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], int(sys.argv[6]) if len(sys.argv) > 6 else 4)
