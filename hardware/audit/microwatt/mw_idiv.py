# Microwatt's integer divisions and remainders, which run inside fpu.vhdl, beside Python integers.
# usage: python3 mw_idiv.py gen SEED N OUT [name ...]   -> OUT.vec, OUT.meta   (N operand pairs per instruction)
#        python3 mw_idiv.py check OUT [examples]        -> report; reads OUT.meta and OUT.out
#        python3 mw_idiv.py one OUT NAME OE RC A:B ...   -> chosen operands (hex)
# Results the Power ISA leaves undefined are not compared: the quotient when the divisor is zero or the
# quotient does not fit, and the upper 32 bits of the word forms. OV and OV32 are compared when OE = 1.
import random
import sys

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1

# name: (kind, extended opcode, has OE, is_32bit, is_signed)     kind 4 OP_DIV, 5 OP_DIVE, 6 OP_MOD
INSN = {
    "divd": (4, 489, 1, 0, 1), "divdu": (4, 457, 1, 0, 0), "divw": (4, 491, 1, 1, 1), "divwu": (4, 459, 1, 1, 0),
    "divde": (5, 425, 1, 0, 1), "divdeu": (5, 393, 1, 0, 0), "divwe": (5, 427, 1, 1, 1), "divweu": (5, 395, 1, 1, 0),
    "modsd": (6, 777, 0, 0, 1), "modud": (6, 265, 0, 0, 0), "modsw": (6, 779, 0, 1, 1), "moduw": (6, 267, 0, 1, 0),
}


def signed(v, w):
    v &= (1 << w) - 1
    return v - (1 << w) if v >> (w - 1) else v


def tdiv(a, b):
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


def ref(name, a, b):
    """-> (value or None when undefined, mask of the defined bits, overflow)"""
    kind, _, _, w32, sg = INSN[name]
    w = 32 if w32 else 64
    mask = (1 << w) - 1
    x, y = a & mask, b & mask
    if sg:
        x, y = signed(x, w), signed(y, w)
    lo, hi = (-(1 << (w - 1)), (1 << (w - 1)) - 1) if sg else (0, mask)
    if y == 0:
        return None, mask, 1
    if kind == 6:
        if sg and x == lo and y == -1:
            return None, mask, 1
        return (x - y * tdiv(x, y)) & mask, mask, 0
    q = tdiv(x << w, y) if kind == 5 else tdiv(x, y)
    if q < lo or q > hi:
        return None, mask, 1
    return q & mask, mask, 0


def encode(name, oe, rc):
    kind, xo, has_oe, w32, sg = INSN[name]
    word = (31 << 26) | (1 << 21) | (2 << 16) | (3 << 11) | ((oe & has_oe) << 10) | (xo << 1) | rc
    flags = (w32 << 7) | (sg << 6) | (1 << 5) | (1 << 4) | (rc << 1) | (oe & has_oe)
    return kind, word, flags


def rnd_len(rng, w):
    n = rng.randint(1, w)
    return rng.getrandbits(n) | (1 << (n - 1))


SPECIAL = [0, 1, 2, 3, M64, M64 - 1, 1 << 63, (1 << 63) - 1, (1 << 63) + 1, 1 << 32, M32, 1 << 31, (1 << 31) - 1,
           (1 << 31) + 1, 0xFFFFFFFF80000000, 0xFFFFFFFF7FFFFFFF, 0x8000000080000000, 0x5555555555555555,
           0xAAAAAAAAAAAAAAAA, 10, 7, 0xFFFFFFFF00000000, 0x00000000FFFFFFFE]


def pairs(rng, name, n):
    kind, _, _, w32, sg = INSN[name]
    w = 32 if w32 else 64
    mask = (1 << w) - 1
    out = []

    def sign(v):
        return (-v) & mask if sg and rng.random() < 0.5 else v & mask

    def put(a, b):
        if w32:  # the upper halves must not matter
            a = (a & M32) | (rng.getrandbits(32) << 32 if rng.random() < 0.5 else 0)
            b = (b & M32) | (rng.getrandbits(32) << 32 if rng.random() < 0.5 else 0)
        out.append((a & M64, b & M64))

    for a in SPECIAL:
        for b in SPECIAL:
            put(a, b)
    while len(out) < n:
        t = rng.randrange(8)
        d = rnd_len(rng, w)
        if t == 0:
            put(sign(rnd_len(rng, w)), sign(d))
        elif t == 1:  # a whole multiple of the divisor, give or take a little
            q = rnd_len(rng, max(1, w - d.bit_length() + 1))
            a = q * d + rng.choice([0, 0, 1, -1, 2, -2, d - 1, d // 2])
            put(sign(a), sign(d))
        elif t == 2:  # powers of two and their neighbours
            k, j = rng.randrange(w), rng.randrange(w)
            put(sign((1 << k) + rng.choice([0, 1, -1])), sign(max(1, (1 << j) + rng.choice([0, 1, -1]))))
        elif t == 3:  # runs of ones
            k, j = rng.randint(1, w), rng.randint(1, w)
            put(sign(((1 << k) - 1) << rng.randrange(w - k + 1)), sign(((1 << j) - 1) << rng.randrange(w - j + 1)))
        elif t == 4:  # the two operands close together
            put(sign(d + rng.choice([0, 1, -1, 2, -2, 3])), sign(d))
        elif t == 5 and kind == 5:  # extended: around the largest quotient that fits
            a = rnd_len(rng, w - 1)
            for b in ((2 * a) & mask, (2 * a + 1) & mask, (2 * a - 1) & mask, a + 1, a, max(1, a - 1)):
                put(sign(a), sign(b))
        elif t == 6 and kind == 5:  # extended: dividend below the divisor
            b = rnd_len(rng, w)
            a = rng.randrange(b) if b > 1 else 0
            put(sign(a >> rng.choice([0, 0, 1, 2, 8])), sign(b))
        else:
            put(rng.getrandbits(64), rng.getrandbits(64))
    return out[:max(n, len(SPECIAL) ** 2)]


def write(vec, meta, name, oe, rc, a, b):
    k, word, flags = encode(name, oe, rc)
    vec.write("%d %08X %02X %016X %016X %016X\n" % (k, word, flags, a, b, 0))
    meta.write("%s %d %d %016x %016x\n" % (name, oe, rc, a, b))


def gen(seed, n, out, names):
    rng = random.Random(seed)
    vec, meta = open(out + ".vec", "w"), open(out + ".meta", "w")
    total = 0
    for name in names:
        for i, (a, b) in enumerate(pairs(rng, name, n)):
            write(vec, meta, name, i & 1, (i >> 1) & 1, a, b)
            total += 1
    vec.close()
    meta.close()
    print("%s: %d instructions" % (out, total))


def one(out, name, oe, rc, items):
    vec, meta = open(out + ".vec", "w"), open(out + ".meta", "w")
    for item in items:
        a, b = (int(x, 16) for x in item.split(":"))
        write(vec, meta, name, oe, rc, a, b)
    vec.close()
    meta.close()


def check(out, examples):
    stats, shown, lat = {}, {}, {}
    res = open(out + ".out")
    for line in open(out + ".meta"):
        name, oe, rc, a, b = line.split()
        oe, rc, a, b = int(oe), int(rc), int(a, 16), int(b, 16)
        f = res.readline().split()
        if len(f) < 7:
            print("result file ends early")
            break
        st = stats.setdefault(name, dict(n=0, value=0, ov=0, cr=0, none=0, undefined=0))
        st["n"] += 1
        bits, data, cycles, xovs = f[0], int(f[1], 16), int(f[3]), f[4]
        crdata, crmask = int(f[5], 16), int(f[6], 16)
        lo, hi = lat.get(name, (cycles, cycles))
        lat[name] = (min(lo, cycles), max(hi, cycles))
        exp, mask, ov = ref(name, a, b)
        has_oe = INSN[name][2]
        why = []
        if cycles == 9999 or bits[0] != "1" or bits[1] != "0":
            st["none"] += 1
            why.append("no answer (%s)" % bits)
        else:
            if exp is None:
                st["undefined"] += 1
            elif bits[2] != "1" or (data & mask) != exp:
                st["value"] += 1
                why.append("value %016x, exact %0*x" % (data, 8 if mask == M32 else 16, exp))
            if oe and has_oe:
                if xovs[0] != "1" or int(xovs[1]) != ov or int(xovs[2]) != ov or int(xovs[3]) != ov:
                    st["ov"] += 1
                    why.append("write_xerc/OV/OV32/SO %s, exact OV %d" % (xovs, ov))
            elif xovs[0] != "0":
                st["ov"] += 1
                why.append("XER written with OE = 0 (%s)" % xovs)
            if rc and exp is not None and mask == M64:
                s = signed(exp, 64)
                want = (8 if s < 0 else 4 if s > 0 else 2) | (ov if (oe and has_oe) else 0)
                got = (crdata >> 28) & 15
                if bits[3] != "1" or not (crmask & 0x80) or got != want:
                    st["cr"] += 1
                    why.append("CR0 %x mask %02x, exact %x" % (got, crmask, want))
            elif not rc and bits[3] == "1":
                st["cr"] += 1
                why.append("CR written with Rc = 0")
        if why:
            key = (name, why[0].split(" ")[0])
            if shown.get(key, 0) < examples:
                shown[key] = shown.get(key, 0) + 1
                print("  %-7s oe %d rc %d a %016x b %016x : %s" % (name, oe, rc, a, b, " | ".join(why)))
    print()
    print("%-8s %9s %7s %7s %7s %7s %10s" % ("insn", "tests", "value", "ov", "cr0", "silent", "undefined"))
    tot = dict(n=0, value=0, ov=0, cr=0, none=0, undefined=0)
    for name, st in stats.items():
        for k in tot:
            tot[k] += st[k]
        print("%-8s %9d %7d %7d %7d %7d %10d" % (name, st["n"], st["value"], st["ov"], st["cr"], st["none"], st["undefined"]))
    print("%-8s %9d %7d %7d %7d %7d %10d" % ("total", tot["n"], tot["value"], tot["ov"], tot["cr"], tot["none"], tot["undefined"]))
    print("clock edges per instruction: " + ", ".join("%s %d to %d" % (n, lo, hi) for n, (lo, hi) in lat.items()))


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5:] or list(INSN))
    elif sys.argv[1] == "one":
        one(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6:])
    else:
        check(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 3)
