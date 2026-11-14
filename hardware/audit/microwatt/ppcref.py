# Exact reference for the Power ISA floating-point instructions of Microwatt's fpu.vhdl.
# Arithmetic is done on fractions and rounded once.
#
# compute(name, a, b, c, rn, en=0) -> Result
#   name   instruction mnemonic (fadd, fadds, fmadd, frsp, fctidz, fcfids, frin, fcmpu, fmr, ...)
#   a b c  the registers FRA, FRB, FRC as 64-bit integers (unused ones are ignored)
#   rn     FPSCR[RN]: 0 nearest even, 1 toward zero, 2 toward +infinity, 3 toward -infinity
#   en     the FPSCR enable bits as they sit in the register: VE 0x80, OE 0x40, UE 0x20, ZE 0x10, XE 0x08.
#          An enabled overflow or underflow returns the rounded result with its exponent moved by 1536
#          (192 in single precision); an enabled invalid operation or zero divide leaves the target alone.
# Result fields
#   bits   the 64-bit register result (None for a compare), mask: the bits of it that are defined
#   write  False when the target register must be left unchanged (enabled invalid operation or zero divide);
#          FR and FI are then 0 and FPRF keeps the value it had
#   cr     the 4-bit compare result FL FG FE FU (compares only)
#   flags  set of FPSCR exception bits raised: OX UX ZX XX VXSNAN VXISI VXIDI VXZDZ VXIMZ VXVC VXSQRT VXCVI
#   fr fi  the FR and FI bits, None where the ISA leaves them undefined or this file does not model them
#   fprf   the five FPRF bits C FL FG FE FU, None where undefined
#   nan    True when an operand was a NaN (the rules for those are kept apart in the report)
from fractions import Fraction
from math import isqrt

M64 = (1 << 64) - 1
SIGN = 1 << 63
QNAN = 0x7FF8000000000000
INF = 0x7FF0000000000000
QBIT = 1 << 51

FPSCR_BIT = {"FX": 31, "FEX": 30, "VX": 29, "OX": 28, "UX": 27, "ZX": 26, "XX": 25, "VXSNAN": 24, "VXISI": 23,
             "VXIDI": 22, "VXZDZ": 21, "VXIMZ": 20, "VXVC": 19, "FR": 18, "FI": 17, "VXSOFT": 10, "VXSQRT": 9,
             "VXCVI": 8}
EXC = ("OX", "UX", "ZX", "XX", "VXSNAN", "VXISI", "VXIDI", "VXZDZ", "VXIMZ", "VXVC", "VXSQRT", "VXCVI")
FPRF_SHIFT = 12


class Fmt:
    def __init__(s, p, emin, emax):
        s.p, s.emin, s.emax = p, emin, emax


DP = Fmt(53, -1022, 1023)
SP = Fmt(24, -126, 127)


EN_VE, EN_OE, EN_UE, EN_ZE, EN_XE = 0x80, 0x40, 0x20, 0x10, 0x08


class Result:
    def __init__(s, bits=None, flags=(), fr=0, fi=0, fprf=None, mask=M64, cr=None, nan=False, write=True):
        s.bits, s.flags, s.fr, s.fi, s.fprf, s.mask, s.cr, s.nan = bits, set(flags), fr, fi, fprf, mask, cr, nan
        s.write = write


def unchanged(flags, nan=False, mask=M64):
    """An enabled invalid operation or zero divide: no result is written, FR FI = 0, FPRF keeps its value (0 here,
    because every test sets the FPSCR to the rounding mode and the enables alone)."""
    return Result(None, flags, fr=0, fi=0, fprf=0, mask=mask, nan=nan, write=False)


def fex(flags, en):
    vx = any(x.startswith("VX") for x in flags)
    return int(bool((vx and en & EN_VE) or ("OX" in flags and en & EN_OE) or ("UX" in flags and en & EN_UE)
                    or ("ZX" in flags and en & EN_ZE) or ("XX" in flags and en & EN_XE)))


def unpack(b):
    """(class, sign, magnitude) with class in zero fin inf qnan snan"""
    s = b >> 63
    e = (b >> 52) & 0x7FF
    f = b & ((1 << 52) - 1)
    if e == 0x7FF:
        if f == 0:
            return "inf", s, None
        return ("qnan" if f & QBIT else "snan"), s, None
    if e == 0:
        if f == 0:
            return "zero", s, Fraction(0)
        return "fin", s, Fraction(f, 1 << 1074)
    m = (1 << 52) | f
    return "fin", s, (Fraction(m << (e - 1075)) if e >= 1075 else Fraction(m, 1 << (1075 - e)))


def ilog2(x):
    """floor(log2(x)) of a positive fraction"""
    n, d = x.numerator, x.denominator
    e = n.bit_length() - d.bit_length()
    if e >= 0:
        if n < (d << e):
            e -= 1
    elif (n << -e) < d:
        e -= 1
    return e


def pack(sign, n, q):
    """the double of magnitude n * 2**q, which must be one"""
    if n == 0:
        return sign << 63
    top = n.bit_length() - 1
    e = top + q
    if e >= -1022:
        if top > 52:
            assert n & ((1 << (top - 52)) - 1) == 0
            frac = n >> (top - 52)
        else:
            frac = n << (52 - top)
        return (sign << 63) | ((e + 1023) << 52) | (frac & ((1 << 52) - 1))
    shift = q + 1074
    assert shift >= 0
    return (sign << 63) | (n << shift)


def fprf_of(bits, f):
    """the FPRF bits of a result held in double format, classed in format f"""
    cls, s, mag = unpack(bits)
    if cls in ("qnan", "snan"):
        return 0b10001
    if cls == "inf":
        return 0b01001 if s else 0b00101
    if cls == "zero":
        return 0b10010 if s else 0b00010
    if ilog2(mag) < f.emin:
        return 0b11000 if s else 0b10100
    return 0b01000 if s else 0b00100


def round_fmt(f, sign, mag, rn, en=0):
    """Round the positive fraction mag to format f. Tininess is detected before rounding."""
    e = ilog2(mag)
    tiny = e < f.emin
    bias = 1536 if f.p == 53 else 192
    trap_u = tiny and bool(en & EN_UE)
    q = (f.emin if (tiny and not trap_u) else e) - (f.p - 1)
    if q >= 0:
        num, den = mag.numerator, mag.denominator << q
    else:
        num, den = mag.numerator << -q, mag.denominator
    n, r = divmod(num, den)
    inexact = r != 0
    if rn == 0:
        inc = 2 * r > den or (2 * r == den and (n & 1) == 1)
    elif rn == 1:
        inc = False
    elif rn == 2:
        inc = inexact and not sign
    else:
        inc = inexact and bool(sign)
    if inc:
        n += 1
        if n >> f.p:
            n >>= 1
            q += 1
    flags = set()
    if n and n.bit_length() - 1 + q > f.emax and (en & EN_OE):
        # enabled overflow: the rounded result with its exponent lowered, a normal number
        bits = pack(sign, n, q - bias)
        # FPRF names a normal number of that sign, whatever range the moved exponent lands in
        return Result(bits, {"OX", "XX"} if inexact else {"OX"}, fr=int(inc), fi=int(inexact),
                      fprf=0b01000 if sign else 0b00100)
    if trap_u:
        # enabled underflow: raised for any tiny result, exact or not; the exponent is raised
        bits = pack(sign, n, q + bias)
        return Result(bits, {"UX", "XX"} if inexact else {"UX"}, fr=int(inc), fi=int(inexact),
                      fprf=0b01000 if sign else 0b00100)
    if n and n.bit_length() - 1 + q > f.emax:
        flags.update(("OX", "XX"))
        to_inf = rn == 0 or (rn == 2 and not sign) or (rn == 3 and sign)
        if to_inf:
            bits = (sign << 63) | INF
        else:
            bits = pack(sign, (1 << f.p) - 1, f.emax - (f.p - 1))
        return Result(bits, flags, fr=None, fi=1, fprf=fprf_of(bits, f))
    if inexact:
        flags.add("XX")
        if tiny:
            flags.add("UX")
    bits = pack(sign, n, q)
    return Result(bits, flags, fr=int(inc), fi=int(inexact), fprf=fprf_of(bits, f))


def round_sqrt(f, mag, rn):
    """Round the square root of the positive fraction mag (a double, so its denominator is a power of 2)."""
    num, den = mag.numerator, mag.denominator
    k = den.bit_length() - 1
    assert den == 1 << k
    if k & 1:
        num <<= 1
        k += 1
    # sqrt(num / 2**k) = sqrt(num) / 2**(k/2); give the integer root at least 2p + 8 bits
    extra = max(0, 2 * f.p + 8 - num.bit_length() // 2)
    num <<= 2 * extra
    root = isqrt(num)
    half = k // 2 + extra
    if root * root == num:
        return round_fmt(f, 0, Fraction(root, 1 << half), rn)
    return round_fmt(f, 0, Fraction(2 * root + 1, 1 << (half + 1)), rn)


def quiet(b):
    return b | QBIT


def exact(bits, f):
    return Result(bits, fprf=fprf_of(bits, f))


def invalid(flag, extra=(), en=0):
    if en & EN_VE:
        return unchanged(set(extra) | {flag})
    return Result(QNAN, set(extra) | {flag}, fprf=0b10001)


def zero_sign(rn):
    return 1 if rn == 3 else 0


ARITH = {"fadd": "add", "fsub": "sub", "fmul": "mul", "fdiv": "div", "fsqrt": "sqrt", "fmadd": "madd",
         "fmsub": "msub", "fnmadd": "nmadd", "fnmsub": "nmsub"}


def arith(base, f, a, b, c, rn, en=0):
    used = {"add": (a, b), "sub": (a, b), "mul": (a, c), "div": (a, b), "sqrt": (b,)}.get(base, (a, b, c))
    ua = [unpack(x) for x in used]
    flags = set()
    if any(u[0] == "snan" for u in ua):
        flags.add("VXSNAN")
    for x, u in zip(used, ua):
        if u[0] in ("qnan", "snan"):
            if base in ("madd", "msub", "nmadd", "nmsub"):
                ka, kc = unpack(a)[0], unpack(c)[0]
                if (ka == "inf" and kc == "zero") or (ka == "zero" and kc == "inf"):
                    flags.add("VXIMZ")
            if flags and (en & EN_VE):
                return unchanged(flags, nan=True)
            return Result(quiet(x), flags, fprf=0b10001, nan=True)
    if base in ("add", "sub"):
        (ka, sa, ma), (kb, sb, mb) = ua
        if base == "sub":
            sb ^= 1
        if ka == "inf" or kb == "inf":
            if ka == "inf" and kb == "inf" and sa != sb:
                return invalid("VXISI", en=en)
            return exact(((sa if ka == "inf" else sb) << 63) | INF, f)
        v = (-ma if sa else ma) + (-mb if sb else mb)
        if v == 0:
            s = sa if (ka == "zero" and kb == "zero" and sa == sb) else zero_sign(rn)
            return exact(s << 63, f)
        return round_fmt(f, int(v < 0), abs(v), rn, en)
    if base == "mul":
        (ka, sa, ma), (kc, sc, mc) = ua
        s = sa ^ sc
        if ka == "inf" or kc == "inf":
            if ka == "zero" or kc == "zero":
                return invalid("VXIMZ", en=en)
            return exact((s << 63) | INF, f)
        if ka == "zero" or kc == "zero":
            return exact(s << 63, f)
        return round_fmt(f, s, ma * mc, rn, en)
    if base == "div":
        (ka, sa, ma), (kb, sb, mb) = ua
        s = sa ^ sb
        if ka == "inf":
            if kb == "inf":
                return invalid("VXIDI", en=en)
            return exact((s << 63) | INF, f)
        if kb == "inf":
            return exact(s << 63, f)
        if kb == "zero":
            if ka == "zero":
                return invalid("VXZDZ", en=en)
            if en & EN_ZE:
                return unchanged({"ZX"})
            return Result((s << 63) | INF, {"ZX"}, fprf=fprf_of((s << 63) | INF, f))
        if ka == "zero":
            return exact(s << 63, f)
        return round_fmt(f, s, ma / mb, rn, en)
    if base == "sqrt":
        kb, sb, mb = ua[0]
        if kb == "zero":
            return exact(sb << 63, f)
        if sb:
            return invalid("VXSQRT", en=en)
        if kb == "inf":
            return exact(INF, f)
        return round_sqrt(f, mb, rn)
    # A * C + B, A * C - B and their negations
    (ka, sa, ma), (kb, sb, mb), (kc, sc, mc) = ua
    if base in ("msub", "nmsub"):
        sb ^= 1
    neg = base in ("nmadd", "nmsub")
    sp = sa ^ sc
    if (ka == "inf" and kc == "zero") or (ka == "zero" and kc == "inf"):
        return invalid("VXIMZ", en=en)
    p_inf = ka == "inf" or kc == "inf"
    if p_inf and kb == "inf" and sp != sb:
        return invalid("VXISI", en=en)
    if p_inf or kb == "inf":
        s = sp if p_inf else sb
        res = exact(((s ^ neg) << 63) | INF, f)
        return res
    p = ma * mc
    v = (-p if sp else p) + (-mb if sb else mb)
    if v == 0:
        s = sp if (p == 0 and mb == 0 and sp == sb) else zero_sign(rn)
        return exact((s ^ neg) << 63, f)
    res = round_fmt(f, int(v < 0), abs(v), rn, en)
    if neg:
        res.bits ^= SIGN
        res.fprf = fprf_of(res.bits, f)
    return res


def to_integer(name, b, rn, en=0):
    res = to_integer_plain(name, b, rn)
    if "VXCVI" in res.flags and (en & EN_VE):
        # enabled invalid operation: the target keeps its value
        return unchanged(res.flags, nan=res.nan, mask=res.mask)
    return res


def to_integer_plain(name, b, rn):
    word = name[4] == "w"
    unsigned = "u" in name[5:]
    if name.endswith("z"):
        rn = 1
    width = 32 if word else 64
    lo, hi = (0, (1 << width) - 1) if unsigned else (-(1 << (width - 1)), (1 << (width - 1)) - 1)
    mask = 0xFFFFFFFF if word else M64
    kb, sb, mb = unpack(b)
    flags = set()

    def out(v):
        return v & ((1 << width) - 1)

    if kb in ("qnan", "snan"):
        flags.add("VXCVI")
        if kb == "snan":
            flags.add("VXSNAN")
        return Result(out(lo), flags, mask=mask, nan=True)
    if kb == "inf":
        return Result(out(lo if sb else hi), {"VXCVI"}, mask=mask)
    n, r = divmod(mb.numerator, mb.denominator)
    den = mb.denominator
    inexact = r != 0
    if rn == 0:
        inc = 2 * r > den or (2 * r == den and (n & 1) == 1)
    elif rn == 1:
        inc = False
    elif rn == 2:
        inc = inexact and not sb
    else:
        inc = inexact and bool(sb)
    v = n + int(inc)
    if sb:
        v = -v
    if v > hi:
        return Result(out(hi), {"VXCVI"}, mask=mask)
    if v < lo:
        return Result(out(lo), {"VXCVI"}, mask=mask)
    return Result(out(v), {"XX"} if inexact else (), fr=int(inc), fi=int(inexact), mask=mask)


def from_integer(name, b, rn):
    f = SP if name.endswith("s") else DP
    v = b if "u" in name[5:] else (b - (1 << 64) if b >> 63 else b)
    if v == 0:
        return exact(0, f)
    return round_fmt(f, int(v < 0), Fraction(abs(v)), rn)


def to_integral(name, b, en=0):
    kb, sb, mb = unpack(b)
    if kb in ("qnan", "snan"):
        if kb == "snan" and (en & EN_VE):
            return unchanged({"VXSNAN"}, nan=True)
        return Result(quiet(b), {"VXSNAN"} if kb == "snan" else (), fprf=0b10001, fr=None, fi=None, nan=True)
    if kb in ("inf", "zero"):
        return Result(b, fprf=fprf_of(b, DP), fr=None, fi=None)
    n, r = divmod(mb.numerator, mb.denominator)
    den = mb.denominator
    inexact = r != 0
    mode = name[3]
    if mode == "n":
        inc = 2 * r >= den
    elif mode == "z":
        inc = False
    elif mode == "p":
        inc = inexact and not sb
    else:
        inc = inexact and bool(sb)
    bits = pack(sb, n + int(inc), 0)
    return Result(bits, fprf=fprf_of(bits, DP), fr=None, fi=None)


def compare(name, a, b, en=0):
    ua, ub = unpack(a), unpack(b)
    flags = set()
    if ua[0] in ("qnan", "snan") or ub[0] in ("qnan", "snan"):
        if ua[0] == "snan" or ub[0] == "snan":
            flags.add("VXSNAN")
            # fcmpo with a signalling NaN sets VXVC as well only while invalid operation is disabled
            if name == "fcmpo" and not (en & EN_VE):
                flags.add("VXVC")
        elif name == "fcmpo":
            flags.add("VXVC")
        return Result(cr=0b0001, flags=flags, fr=None, fi=None, nan=True)

    def val(u):
        if u[0] == "inf":
            return Fraction(-(1 << 2000)) if u[1] else Fraction(1 << 2000)
        return -u[2] if u[1] else u[2]

    x, y = val(ua), val(ub)
    return Result(cr=0b1000 if x < y else 0b0100 if x > y else 0b0010, fr=None, fi=None)


def move(name, a, b, c):
    if name == "fmr":
        v = b
    elif name == "fneg":
        v = b ^ SIGN
    elif name == "fabs":
        v = b & ~SIGN & M64
    elif name == "fnabs":
        v = b | SIGN
    elif name == "fcpsgn":
        v = (a & SIGN) | (b & ~SIGN & M64)
    else:   # fsel: (FRA) >= 0.0 selects FRC, anything else (a NaN too) selects FRB
        ka, sa, _ = unpack(a)
        v = c if (ka == "zero" or (ka in ("fin", "inf") and not sa)) else b
    return Result(v, fr=None, fi=None)


def compute(name, a, b, c, rn, en=0):
    base = name[:-1] if name.endswith("s") and name[:-1] in ARITH else name
    if base in ARITH:
        return arith(ARITH[base], SP if name != base else DP, a, b, c, rn, en)
    if name == "frsp":
        kb, sb, mb = unpack(b)
        if kb in ("qnan", "snan"):
            if kb == "snan" and (en & EN_VE):
                return unchanged({"VXSNAN"}, nan=True)
            return Result(quiet(b) & ~((1 << 29) - 1), {"VXSNAN"} if kb == "snan" else (), fprf=0b10001, nan=True)
        if kb in ("inf", "zero"):
            return exact(b, SP)
        return round_fmt(SP, sb, mb, rn, en)
    if name.startswith("fcti"):
        return to_integer(name, b, rn, en)
    if name.startswith("fcfid"):
        return from_integer(name, b, rn)
    if name in ("frin", "friz", "frip", "frim"):
        return to_integral(name, b, en)
    if name in ("fcmpu", "fcmpo"):
        return compare(name, a, b, en)
    return move(name, a, b, c)


def single_to_double(w):
    """the double-format register that holds the single with bit pattern w"""
    s = (w >> 31) & 1
    e = (w >> 23) & 0xFF
    fr = w & 0x7FFFFF
    if e == 0xFF:
        return (s << 63) | INF | (fr << 29)
    if e == 0:
        if fr == 0:
            return s << 63
        return pack(s, fr, -149)
    return (s << 63) | ((e - 127 + 1023) << 52) | (fr << 29)
