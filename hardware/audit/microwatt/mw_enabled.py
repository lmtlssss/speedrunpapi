# Microwatt's fpu.vhdl with the FPSCR exception enables set, beside ppcref.py.
# usage: python3 mw_enabled.py gen SEED N OUT [name ...]      -> OUT.vec, OUT.meta   (N operand sets per instruction)
#        python3 mw_enabled.py genpre SEED N OUT [name ...]   the same with the FPSCR's other bits filled in first
#        python3 mw_enabled.py check OUT [examples]
#        python3 mw_enabled.py one OUT NAME RN EN A:B:C ...   chosen operands, hex; RN may be "all",
#                                                            and @FILE reads one A:B:C per line
# Every operand set is run under seven settings of the enables (none, XE, ZE, UE, OE, VE, all five) with a
# rounding mode drawn per test. Each test is mtfsf (FPSCR := rounding mode and enables), the instruction, mffs.
# The unit is driven with MSR[FE0 FE1] = 00, so no interrupt is expected; the FPSCR and the target still follow
# the enabled rules: an enabled invalid operation or zero divide writes nothing, an enabled overflow or
# underflow writes the rounded result with its exponent moved by 1536 (192 for the single forms and frsp).
#
# genpre also draws the sticky exception bits, FX, FR, FI and FPRF that mtfsf writes before the instruction.
# After it, an exception bit is set if it was set or is raised, FX if it was set or a bit went from 0 to 1,
# VX and FEX are the summaries, and FR, FI and FPRF are what the instruction's kind says: arithmetic sets
# them, a compare sets only the four FPCC bits, a move changes nothing, and an instruction that writes no
# result clears FR and FI and leaves FPRF.
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mwinsn as mc
import ppcref
from ppcref import FPSCR_BIT, FPRF_SHIFT, M64, INF, QBIT

ENS = [0x00, 0x08, 0x10, 0x20, 0x40, 0x80, 0xF8]
ENN = {0x00: "none", 0x08: "XE", 0x10: "ZE", 0x20: "UE", 0x40: "OE", 0x80: "VE", 0xF8: "all"}
MOVES = ("fmr", "fneg", "fabs", "fnabs", "fcpsgn", "fsel")
NAMES = [n for n in mc.INSN if n not in MOVES]
STICKY = ("OX", "UX", "ZX", "XX", "VXSNAN", "VXISI", "VXIDI", "VXZDZ", "VXIMZ", "VXVC", "VXSOFT", "VXSQRT", "VXCVI")
DEXP = [0, 0, 1, 2, 3, 52, 53, 54, 500, 511, 512, 513, 1000, 1022, 1023, 1024, 1025, 1500, 1535, 1536, 1537, 2000,
        2044, 2045, 2046]
SEXP = [0, 0, 1, 2, 3, 23, 24, 25, 62, 63, 64, 96, 126, 127, 128, 129, 150, 190, 191, 192, 193, 252, 253, 254]


def pattern(rng, bits):
    full = (1 << bits) - 1
    return rng.choice([0, 0, 1, full, full - 1, 1 << (bits - 1), (1 << (bits - 1)) - 1, rng.getrandbits(bits),
                       rng.getrandbits(bits), rng.getrandbits(bits) & ~((1 << rng.randrange(bits)) - 1)])


def double(rng):
    k = rng.randrange(24)
    s = rng.getrandbits(1) << 63
    if k == 0:
        return s
    if k == 1:
        return s | INF
    if k == 2:
        return s | INF | QBIT | rng.getrandbits(20)
    if k == 3:
        return s | INF | ((rng.getrandbits(50) | 1) & ~QBIT)
    e = rng.choice(DEXP) if rng.random() < 0.8 else rng.randrange(2047)
    return s | (e << 52) | pattern(rng, 52)


def single(rng):
    k = rng.randrange(24)
    s = rng.getrandbits(1) << 31
    if k == 0:
        w = s
    elif k == 1:
        w = s | 0x7F800000
    elif k == 2:
        w = s | 0x7FC00000 | rng.getrandbits(10)
    elif k == 3:
        w = s | 0x7F800000 | ((rng.getrandbits(21) | 1) & 0x3FFFFF)
    else:
        e = rng.choice(SEXP) if rng.random() < 0.8 else rng.randrange(255)
        w = s | (e << 23) | pattern(rng, 23)
    return ppcref.single_to_double(w)


def operands(rng, name):
    base = name[:-1] if name.endswith("s") and name[:-1] in ppcref.ARITH else name
    if name.startswith("fcfid"):
        n = rng.choice([64, 64, 53, 54, 25, 26, 27, 40, 63, 1, 8])
        v = pattern(rng, n) | (1 << (n - 1) if rng.random() < 0.7 else 0)
        if rng.random() < 0.3:
            v = (-v) & M64
        return 0, v & M64, 0
    draw = single if (base in ppcref.ARITH and base != name) else double
    x, y, z = draw(rng), draw(rng), draw(rng)
    if name in MOVES:
        return x, y, z
    kind = ppcref.ARITH.get(base)
    if kind in ("add", "sub", "div"):
        if kind == "div" and rng.random() < 0.15:
            y &= 1 << 63          # divide by zero
        return x, y, 0
    if kind == "mul":
        return x, 0, y
    if kind == "sqrt":
        return 0, x, 0
    if kind is not None:
        return x, z, y
    if mc.ROWS[name]["a"]:
        return x, y, 0
    return 0, x, 0


def write(vec, meta, name, rn, en, a, b, c, pre=None, rc=0):
    k, word, flags = mc.encode(name)
    if rc:                      # the record form: CR field 1 := FX FEX VX OX
        word |= 1
        flags |= 2
    vec.write("2 %08X 10 %016X %016X %016X\n" % (mc.MTFSF, 0, (rn | en) if pre is None else pre, 0))
    vec.write("%d %08X %02X %016X %016X %016X\n" % (k, word, flags, a, b, c))
    vec.write("2 %08X 10 %016X %016X %016X\n" % (mc.MFFS, 0, 0, 0))
    meta.write("%s %d %016x %016x %016x %02x%s\n" % (name, rn, a, b, c, en,
                                                    "" if pre is None else " %08x %d" % (pre, rc)))


def gen(seed, n, out, names, with_pre=False):
    rng = random.Random(seed)
    vec, meta = open(out + ".vec", "w"), open(out + ".meta", "w")
    total = 0
    for name in names:
        for _ in range(n):
            a, b, c = operands(rng, name)
            for en in ENS:
                rn = rng.randrange(4)
                pre, rc = None, 0
                if with_pre:
                    pre = rn | en | (rng.getrandbits(1) << 31) | (rng.getrandbits(2) << 17) | (rng.getrandbits(5) << 12)
                    for f in STICKY:
                        if rng.random() < 0.3:
                            pre |= 1 << FPSCR_BIT[f]
                    if with_pre == "rc" and kind_of(name) != "cmp":
                        rc = rng.getrandbits(1)
                write(vec, meta, name, rn, en, a, b, c, pre, rc)
                total += 1
    vec.close()
    meta.close()
    print("%s: %d tests, %d instructions" % (out, total, 3 * total))


def one(out, name, rn, en, items):
    if len(items) == 1 and items[0].startswith("@"):
        items = open(items[0][1:]).read().split()
    vec, meta = open(out + ".vec", "w"), open(out + ".meta", "w")
    for item in items:
        f = (item.split(":") + ["", "", ""])[:3]
        a, b, c = (int(x, 16) if x else 0 for x in f)
        for mode in (range(4) if rn == "all" else [int(rn)]):
            write(vec, meta, name, mode, en, a, b, c)
    vec.close()
    meta.close()


def kind_of(name):
    if name in MOVES:
        return "move"
    if name in ("fcmpu", "fcmpo"):
        return "cmp"
    if name.startswith("fcti"):
        return "cti"
    if name in ("frin", "friz", "frip", "frim"):
        return "fri"
    return "arith"


def check(out, examples):
    stats, shown = {}, {}
    res = open(out + ".out")
    total = 0
    for line in open(out + ".meta"):
        f = line.split()
        name, rn, a, b, c, en = f[0], int(f[1]), int(f[2], 16), int(f[3], 16), int(f[4], 16), int(f[5], 16)
        pre = int(f[6], 16) if len(f) > 6 else (rn | en)
        rc = int(f[7]) if len(f) > 7 else 0
        l1, l2, l3 = res.readline().split(), res.readline().split(), res.readline().split()
        if len(l3) < 4:
            print("result file ends after %d tests" % total)
            break
        total += 1
        st = stats.setdefault((name, en), dict(n=0, value=0, write=0, flags=0, second=0, none=0, intr=0))
        st["n"] += 1
        exp = ppcref.compute(name, a, b, c, rn, en)
        kind = kind_of(name)
        bits, data, cr, cycles = l2[0], int(l2[1], 16), int(l2[2], 16), int(l2[3])
        fpscr = int(l3[1], 16) & 0xFFFFFFFF
        why = []
        if cycles == 9999 or l3[0][0] != "1" or (bits[0] != "1" and bits[1] != "1"):
            st["none"] += 1
            why.append("no answer")
        else:
            if bits[1] == "1":
                st["intr"] += 1
                why.append("interrupt raised with FE0 FE1 = 00")
            if not exp.write:
                if bits[2] == "1":
                    st["write"] += 1
                    why.append("wrote %016x where the target must keep its value" % data)
            elif exp.bits is not None:
                if bits[2] != "1":
                    st["write"] += 1
                    why.append("wrote nothing, exact %016x" % (exp.bits & exp.mask))
                elif (data & exp.mask) != (exp.bits & exp.mask):
                    st["value"] += 1
                    why.append("value %016x, exact %016x" % (data & exp.mask, exp.bits & exp.mask))
            if exp.cr is not None:
                if bits[3] != "1" or cr != exp.cr or ((fpscr >> FPRF_SHIFT) & 15) != exp.cr:
                    st["value"] += 1
                    why.append("compare %x, fpcc %x, exact %x" % (cr, (fpscr >> FPRF_SHIFT) & 15, exp.cr))
            # the exception bits, FX, VX and FEX after the instruction
            before = {x for x in STICKY if (pre >> FPSCR_BIT[x]) & 1}
            want = before | exp.flags
            want_fx = ((pre >> 31) & 1) | int(bool(exp.flags - before))
            want_vx = int(any(x.startswith("VX") for x in want))
            want_fex = ppcref.fex(want, en)
            got = {x for x in STICKY if (fpscr >> FPSCR_BIT[x]) & 1}
            got_fx, got_vx, got_fex = (fpscr >> 31) & 1, (fpscr >> FPSCR_BIT["VX"]) & 1, (fpscr >> FPSCR_BIT["FEX"]) & 1
            if got != want or got_fx != want_fx or got_vx != want_vx or got_fex != want_fex:
                st["flags"] += 1
                why.append("flags %s FX %d FEX %d, exact %s FX %d FEX %d (before: %s)"
                           % (" ".join(sorted(got)) or "none", got_fx, got_fex, " ".join(sorted(want)) or "none",
                              want_fx, want_fex, " ".join(sorted(before)) or "none"))
            # FR, FI and FPRF
            pre_fr, pre_fi, pre_fprf = (pre >> 18) & 1, (pre >> 17) & 1, (pre >> FPRF_SHIFT) & 31
            if kind == "move":
                want_fr, want_fi, want_fprf = pre_fr, pre_fi, pre_fprf
            elif kind == "cmp":
                want_fr, want_fi, want_fprf = pre_fr, pre_fi, (pre_fprf & 16) | exp.cr
            elif kind == "fri":
                want_fr, want_fi, want_fprf = 0, 0, (exp.fprf if exp.write else pre_fprf)
            elif kind == "cti":
                want_fr, want_fi, want_fprf = exp.fr, exp.fi, (None if exp.write else pre_fprf)
            else:
                want_fr, want_fi, want_fprf = exp.fr, exp.fi, (exp.fprf if exp.write else pre_fprf)
            sec = []
            if want_fr is not None and ((fpscr >> FPSCR_BIT["FR"]) & 1) != want_fr:
                sec.append("FR %d, exact %d" % ((fpscr >> FPSCR_BIT["FR"]) & 1, want_fr))
            if want_fi is not None and ((fpscr >> FPSCR_BIT["FI"]) & 1) != want_fi:
                sec.append("FI %d, exact %d" % ((fpscr >> FPSCR_BIT["FI"]) & 1, want_fi))
            if want_fprf is not None and ((fpscr >> FPRF_SHIFT) & 31) != want_fprf:
                sec.append("FPRF %s, exact %s" % (format((fpscr >> FPRF_SHIFT) & 31, "05b"), format(want_fprf, "05b")))
            if (fpscr & 0xFF) != (pre & 0xFF):
                sec.append("enables and rounding mode %02x, were %02x" % (fpscr & 0xFF, pre & 0xFF))
            if rc and len(l2) >= 7:
                cr1, mask = (int(l2[5], 16) >> 24) & 15, int(l2[6], 16)
                if bits[3] != "1" or not (mask & 0x40) or cr1 != (fpscr >> 28) & 15:
                    sec.append("CR1 %x (written %s, mask %02x), FPSCR's FX FEX VX OX %x" % (cr1, bits[3], mask, (fpscr >> 28) & 15))
            elif kind != "cmp" and bits[3] == "1":
                sec.append("CR written by a form that does not record")
            if sec:
                st["second"] += 1
                why.append("; ".join(sec))
        if why:
            key = (name, en, why[0].split(" ")[0])
            if shown.get(key, 0) < examples:
                shown[key] = shown.get(key, 0) + 1
                print("  %-8s %-4s %-7s a %016x b %016x c %016x fpscr %08x -> %08x : %s"
                      % (name, ENN.get(en, "%02x" % en), mc.RNN[rn], a, b, c, pre, fpscr, " | ".join(why)))
    print()
    print("%-9s %-5s %8s %7s %7s %7s %8s %7s %7s" % ("insn", "en", "tests", "value", "write", "flags", "fr/fi/c", "silent", "intr"))
    tot = dict(n=0, value=0, write=0, flags=0, second=0, none=0, intr=0)
    for (name, en), st in stats.items():
        for k in tot:
            tot[k] += st[k]
        if any(st[k] for k in ("value", "write", "flags", "second", "none", "intr")):
            print("%-9s %-5s %8d %7d %7d %7d %8d %7d %7d" % (name, ENN.get(en, "%02x" % en), st["n"], st["value"], st["write"],
                                                             st["flags"], st["second"], st["none"], st["intr"]))
    print("%-9s %-5s %8d %7d %7d %7d %8d %7d %7d" % ("total", "", tot["n"], tot["value"], tot["write"], tot["flags"],
                                                     tot["second"], tot["none"], tot["intr"]))


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5:] or NAMES)
    elif sys.argv[1] in ("genpre", "genrc"):
        gen(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5:] or list(mc.INSN),
            with_pre="rc" if sys.argv[1] == "genrc" else True)
    elif sys.argv[1] == "one":
        one(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5], 16), sys.argv[6:])
    else:
        check(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 3)
