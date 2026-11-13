# blif2aig.py: turn a LUT netlist (BLIF) into an AND/OR graph (binary AIGER) in which every LUT that
# depends on the symbolic inputs is present twice: once as an irredundant cover of its function and
# once as an irredundant cover of its complement. Internal signals are then never negated, so the
# graph can be multiplied out directly. Every cover is checked against the LUT's truth table.
#
# usage: blif2aig.py in.blif out.aig FIRST_SYM NUM_SYM POL
#   inputs FIRST_SYM .. FIRST_SYM+NUM_SYM-1 are the symbolic ones (A and B)
#   POL = 1: the outputs written are the complements of the netlist outputs
import sys, re
M6 = [0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0, 0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000, 0xFFFFFFFF00000000]
FULL = (1 << 64) - 1

def rep(tt, k):
    w = 1 << k; tt &= (1 << w) - 1
    while w < 64: tt |= tt << w; w <<= 1
    return tt

def cof(t, j, v):
    s = 1 << j
    if v: c = t & M6[j]; return c | (c >> s)
    c = t & ~M6[j] & FULL; return c | (c << s)

def isop(L, U, k):
    """Minato-Morreale: cover C with L <= C <= U. Cubes are (mask, value) over inputs 0..k-1."""
    if L == 0: return [], 0
    if U == FULL: return [(0, 0)], FULL
    j = k - 1
    while j >= 0 and cof(L, j, 0) == cof(L, j, 1) and cof(U, j, 0) == cof(U, j, 1): j -= 1
    assert j >= 0
    L0, L1, U0, U1 = cof(L, j, 0), cof(L, j, 1), cof(U, j, 0), cof(U, j, 1)
    c0, f0 = isop(L0 & ~U1 & FULL, U0, j)
    c1, f1 = isop(L1 & ~U0 & FULL, U1, j)
    c2, f2 = isop((L0 & ~f0 & FULL) | (L1 & ~f1 & FULL), U0 & U1, j)
    cov = [(m | (1 << j), v) for m, v in c0] + [(m | (1 << j), v | (1 << j)) for m, v in c1] + c2
    return cov, (f0 & ~M6[j] & FULL) | (f1 & M6[j]) | f2

class Aig:
    def __init__(s, ni): s.ni = ni; s.ands = []; s.h = {}
    def AND(s, a, b):
        if a > b: a, b = b, a
        if a == 0 or a == (b ^ 1): return 0
        if a == 1 or a == b: return b
        k = (a, b)
        if k not in s.h: s.ands.append(k); s.h[k] = 2 * (s.ni + len(s.ands))
        return s.h[k]
    def OR(s, a, b): return s.AND(a ^ 1, b ^ 1) ^ 1
    def write(s, path, outs):
        def enc(x):
            o = bytearray()
            while x & ~0x7f: o.append((x & 0x7f) | 0x80); x >>= 7
            o.append(x); return bytes(o)
        with open(path, "wb") as f:
            f.write(f"aig {s.ni + len(s.ands)} {s.ni} 0 {len(outs)} {len(s.ands)}\n".encode())
            for o in outs: f.write(f"{o}\n".encode())
            for i, (a, b) in enumerate(s.ands):
                lhs = 2 * (s.ni + i + 1); f.write(enc(lhs - b) + enc(b - a))

blif, outp, first, num, pol = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
txt = open(blif).read()
ins = re.search(r"(?m)^\.inputs (.*)$", txt).group(1).split()
outs = re.search(r"(?m)^\.outputs (.*)$", txt).group(1).split()
g = Aig(len(ins))
pos, neg, sym = {}, {}, {}
for i, nm in enumerate(ins):
    pos[nm] = 2 * (i + 1); neg[nm] = 2 * (i + 1) + 1; sym[nm] = first <= i < first + num
nl = ncov = 0
blocks = re.split(r"(?m)^(?=\.names )", txt)[1:]
fanin = {b.split("\n")[0].split()[-1]: b.split("\n")[0].split()[1:-1] for b in blocks}
need, stack = set(), list(outs)          # only the logic that reaches an output
while stack:
    v = stack.pop()
    if v in need or v not in fanin: continue
    need.add(v); stack.extend(fanin[v])
for blk in blocks:
    if blk.split("\n")[0].split()[-1] not in need: continue
    lines = blk.split(".end")[0].strip().split("\n")
    names = lines[0].split()[1:]; fan, out = names[:-1], names[-1]; k = len(fan)
    assert k <= 6
    tt = 0
    for ln in lines[1:]:
        ln = ln.split()
        if not ln: continue
        pat, val = (ln[0], ln[1]) if len(ln) == 2 else ("", ln[0])
        assert val == "1"
        for m in range(1 << k):
            if all(ch == "-" or int(ch) == (m >> j) & 1 for j, ch in enumerate(pat)): tt |= 1 << m
    t = rep(tt, k) if k else (FULL if tt & 1 else 0)
    sy = any(sym[u] for u in fan)
    def build(cov):
        acc = 0
        for m, v in cov:
            c = 1
            for j in range(k):
                if (m >> j) & 1: c = g.AND(c, pos[fan[j]] if (v >> j) & 1 else neg[fan[j]])
            acc = g.OR(acc, c)
        return acc
    cp, fp = isop(t, t, k); assert fp == t
    pos[out] = build(cp); nl += 1; ncov += len(cp)
    if sy:
        cn, fn = isop(~t & FULL, ~t & FULL, k); assert fn == (~t & FULL)
        neg[out] = build(cn); ncov += len(cn)
    else:
        neg[out] = pos[out] ^ 1
    sym[out] = sy
g.write(outp, [(neg[o] if pol else pos[o]) for o in outs])
print(f"{blif}: {nl} LUTs, {sum(1 for v in sym.values() if v) - num} depend on the symbolic inputs, {len(g.ands)} AND nodes")
