"""Multiplier compiler: n x n unsigned -> 2n-bit product as a k-LUT network (k = 6).

Contract: for all inputs, sum(2^c * f[c]) = a * b.
Method: recursive split  X*Y = Z0 + 2^(2h) Z2 + 2^h (P - Z0 - Z2),  P = (Xl+Xh)(Yl+Yh).
Z0 and Z2 are retained as single words and observed twice (once negated); a negated wire is an
inverted input of the consuming LUT plus a constant, so the reuse builds no logic.  Leaves are
radix-4 recoded rows in a bit heap.  Every addition ends in one LUT per bit: the carry into
column c is recovered from column c-1's wires and its sum bit.
"""
import argparse
import hashlib
import json
import random
from functools import lru_cache
from pathlib import Path

SCHEMA = "colony.lut-mul.v1"


class Net:
    def __init__(self, k=6):
        self.k, self.luts, self.level, self.count = k, [], {}, 0

    def lut(self, ins, fn):
        tt = 0
        for row in range(1 << len(ins)):
            if fn([(row >> i) & 1 for i in range(len(ins))]):
                tt |= 1 << row
        self.count += 1
        o = "n%d" % self.count
        self.luts.append((o, list(ins), tt))
        self.level[o] = 1 + max([self.level.get(v, 0) for v in ins] + [0])
        return o


# atom = (vars tuple, truth table int).  value in {0,1}.
def W(w):
    return ((w,), 0b10)


def NOT(w):
    return ((w,), 0b01)


ONE = ((), 1)


def aval(atom, env):
    vs, tt = atom
    r = 0
    for i, v in enumerate(vs):
        r |= env[v] << i
    return (tt >> r) & 1


@lru_cache(maxsize=None)
def _plan(h, u):
    if h <= 2:
        return (0, ())
    cands = []
    if h >= 6:
        cands.append((0, "6", h - 5, u))
    if h >= 5 and u >= 1:
        cands.append((0, "51", h - 4, u))
    cands.append((1, "fa", h - 2, u))
    if h >= 4 and u >= 1:
        cands.append((1, "41", h - 3, u))
    if h >= 5:
        cands.append((1, "5", h - 4, u))
    if u >= 2:
        cands.append((1, "32", h - 2, u - 1))
    best = None
    for w, op, nh, nu in cands:
        sub = _plan(nh, nu)
        if best is None or w + sub[0] < best[0]:
            best = (w + sub[0], (op,) + sub[1])
    return best


TAKE = {"6": (6, 0), "51": (5, 1), "fa": (3, 0), "41": (4, 1), "5": (5, 0), "32": (3, 2)}


def counter(net, cols, group, col):
    """group: list of (atom, column). Emits the binary digits of the weighted sum into cols."""
    vars_ = []
    for a, _ in group:
        for v in a[0]:
            if v not in vars_:
                vars_.append(v)
    assert len(vars_) <= net.k
    wts = [1 << (c - col) for _, c in group]
    for d in range(sum(wts).bit_length()):
        def fn(bits, d=d):
            env = dict(zip(vars_, bits))
            return (sum(w for (a, _), w in zip(group, wts) if aval(a, env)) >> d) & 1
        vals = [fn([(row >> i) & 1 for i in range(len(vars_))]) for row in range(1 << len(vars_))]
        if not any(vals):
            continue
        if all(vals):
            cols.setdefault(col + d, []).append(ONE)
            continue
        cols.setdefault(col + d, []).append(W(net.lut(vars_, fn)))


def reduce_pair(net, cols, width):
    """cols: {column: [atoms]} with value known to lie in [0, 2^width) modulo 2^width.
    Returns a word: list of atoms (wire, inverted wire, constant, or None for zero) per bit."""
    for c in list(cols):
        if c >= width:
            del cols[c]
    lvl = lambda a: max([net.level.get(v, 0) for v in a[0]] + [0])
    for c in range(width):
        col = cols.setdefault(c, [])
        ones = sum(1 for a in col if a == ONE)                 # constants fold arithmetically
        col[:] = [a for a in col if a != ONE]
        if ones:
            if ones & 1:
                col.append(ONE)
            for d in range(1, ones.bit_length()):
                if (ones >> d) & 1 and c + d < width:
                    cols.setdefault(c + d, []).append(ONE)
        multi = [a for a in col if len(a[0]) > 1]              # product atoms
        while multi:
            g = [multi.pop(0)]
            vs = set(g[0][0])
            for a in list(multi):
                if len(vs | set(a[0])) <= net.k and len(g) < 3:
                    g.append(a)
                    vs |= set(a[0])
                    multi.remove(a)
            for a in g:
                col.remove(a)
            counter(net, cols, [(a, c) for a in g], c)
        while True:                                            # zero-waste counters only: 6:3 and 5+1:3
            wires = [a for a in col if a != ONE]
            const = [a for a in col if a == ONE]
            nxt = cols.setdefault(c + 1, []) if c + 1 < width else []
            u = [a for a in nxt if len(a[0]) == 1]
            wires.sort(key=lvl)
            u.sort(key=lvl)
            if len(wires) >= 6 and (len(wires) != 6 or True):
                g = [(a, c) for a in wires[:6] + const]
            elif len(wires) == 5 and u:
                g = [(a, c) for a in wires[:5] + const] + [(u[0], c + 1)]
            else:
                break
            for a, cc in g:
                cols[cc].remove(a)
            counter(net, cols, g, c)
            for cc in list(cols):
                if cc >= width:
                    del cols[cc]
    # rows are then added pairwise: one LUT per bit, carry recovered from the previous column
    while max([len(v) for v in cols.values()] + [0]) > 1:
        prev, prev_s, carry = [], None, False
        for c in range(width):
            col = cols.setdefault(c, [])
            col.sort(key=lambda a: (a != ONE, lvl(a)))
            take = 3 if (not carry and col and col[0] == ONE) else 2     # a chain may start with a constant
            atoms, rest = col[:take], col[take:]
            if not carry and len(atoms) <= 1:
                prev, prev_s, carry = atoms, None, False
                continue
            vars_ = []
            for a in atoms + (prev if carry else []):
                for v in a[0]:
                    if v not in vars_:
                        vars_.append(v)
            if carry and prev_s is not None:
                vars_.append(prev_s)

            def fn(bits, atoms=atoms, prev=prev, prev_s=prev_s, carry=carry, vars_=vars_):
                env = dict(zip(vars_, bits))
                cin = 0
                if carry:
                    sp = sum(aval(a, env) for a in prev)
                    vin = 0 if prev_s is None else (env[prev_s] ^ (sp & 1))
                    cin = (sp + vin) >> 1
                return (sum(aval(a, env) for a in atoms) + cin) & 1
            o = net.lut(vars_, fn)
            carry_next = (len(atoms) + (1 if carry else 0)) >= 2
            prev, prev_s, carry = atoms, (o if carry else None), carry_next
            cols[c] = [W(o)] + rest
    return [cols[c][0] if cols.get(c) else None for c in range(width)]


def reduce_plan(net, cols, width):
    for c in list(cols):
        if c >= width:
            del cols[c]
    lvl = lambda a: max([net.level.get(v, 0) for v in a[0]] + [0])
    for c in range(width):
        col = cols.setdefault(c, [])
        ones = sum(1 for a in col if a == ONE)
        col[:] = [a for a in col if a != ONE]
        if ones:
            if ones & 1:
                col.append(ONE)
            for d in range(1, ones.bit_length()):
                if (ones >> d) & 1 and c + d < width:
                    cols.setdefault(c + d, []).append(ONE)
        multi = [a for a in col if len(a[0]) > 1]
        while multi:
            g = [multi.pop(0)]
            vs = set(g[0][0])
            for a in list(multi):
                if len(vs | set(a[0])) <= net.k and len(g) < 3:
                    g.append(a)
                    vs |= set(a[0])
                    multi.remove(a)
            for a in g:
                col.remove(a)
            counter(net, cols, [(a, c) for a in g], c)
        while len(col) > 2:
            const = [a for a in col if a == ONE]
            wires = [a for a in col if a != ONE]
            nxt = cols.setdefault(c + 1, []) if c + 1 < width else []
            u = [a for a in nxt if len(a[0]) == 1]
            op = _plan(len(wires), min(len(u), 6))[1]
            if not op:
                g = [(a, c) for a in wires + const]
            else:
                t = TAKE[op[0]]
                wires.sort(key=lvl)
                u.sort(key=lvl)
                g = [(a, c) for a in wires[:t[0]] + const] + [(a, c + 1) for a in u[:t[1]]]
            for a, cc in g:
                cols[cc].remove(a)
            counter(net, cols, g, c)
            for cc in list(cols):
                if cc >= width:
                    del cols[cc]
    word, prev, prev_s, carry = [], [], None, False
    for c in range(width):
        atoms = list(cols.get(c, []))
        if not carry and len(atoms) <= 1:
            word.append(atoms[0] if atoms else None)
            prev, prev_s, carry = atoms, None, False
            continue
        vars_ = []
        for a in atoms + (prev if carry else []):
            for v in a[0]:
                if v not in vars_:
                    vars_.append(v)
        if carry and prev_s is not None:
            vars_.append(prev_s)

        def fn(bits, atoms=atoms, prev=prev, prev_s=prev_s, carry=carry, vars_=vars_):
            env = dict(zip(vars_, bits))
            cin = 0
            if carry:
                sp = sum(aval(a, env) for a in prev)
                vin = 0 if prev_s is None else (env[prev_s] ^ (sp & 1))
                cin = (sp + vin) >> 1
            return (sum(aval(a, env) for a in atoms) + cin) & 1
        o = net.lut(vars_, fn)
        word.append(W(o))
        carry_next = (len(atoms) + (1 if carry else 0)) >= 2
        prev, prev_s, carry = atoms, (o if carry else None), carry_next
    return word


def reduce_heap(net, cols, width):
    """Both reductions are run; the smaller network is kept."""
    return best_of(net, [lambda: reduce_plan(net, {c: list(v) for c, v in cols.items()}, width),
                         lambda: reduce_pair(net, {c: list(v) for c, v in cols.items()}, width)])


def put(cols, word, shift, sign, consts, width):
    for i, a in enumerate(word):
        c = i + shift
        if a is None or c >= width:
            continue
        if sign > 0:
            cols.setdefault(c, []).append(a)
        elif a == ONE:
            consts[0] -= 1 << c
        else:                                                   # -a = (1-a) - 1
            vs, tt = a
            cols.setdefault(c, []).append((vs, tt ^ 0b11))
            consts[0] -= 1 << c


def close(net, cols, consts, width):
    kk = consts[0] % (1 << width)
    for c in range(width):
        if (kk >> c) & 1:
            cols.setdefault(c, []).append(ONE)
    return reduce_heap(net, cols, width)


def booth_leaf(net, X, Y):
    """X, Y: words of plain wire atoms (or None). Returns word of X*Y."""
    n, m = len(X), len(Y)
    width = n + m
    cols, consts = {}, [0]
    xs = [a for a in X]
    yv = lambda i: Y[i] if 0 <= i < m else None
    for i in range(0, (m + 2) // 2 + 1):
        y0, y1, y2 = yv(2 * i - 1), yv(2 * i), yv(2 * i + 1)
        if y1 is None and y2 is None and y0 is None:
            continue
        ys = [a for a in (y0, y1, y2)]
        for j in range(n + 1):
            xa = xs[j] if j < n else None
            xb = xs[j - 1] if j >= 1 else None
            parts = [a for a in ys + [xa, xb] if a is not None]
            vars_ = []
            for a in parts:
                for v in a[0]:
                    if v not in vars_:
                        vars_.append(v)

            def fn(bits, vars_=vars_, ys=ys, xa=xa, xb=xb):
                env = dict(zip(vars_, bits))
                g = lambda a: 0 if a is None else aval(a, env)
                d = g(ys[0]) + g(ys[1]) - 2 * g(ys[2])
                mj = g(xa) if abs(d) == 1 else (g(xb) if abs(d) == 2 else 0)
                return mj ^ g(ys[2])
            vals = [fn([(r >> t) & 1 for t in range(len(vars_))]) for r in range(1 << len(vars_))]
            c = 2 * i + j
            if c >= width or not any(vals):
                continue
            tt = sum(v << r for r, v in enumerate(vals))
            cols.setdefault(c, []).append((tuple(vars_), tt))
        if y2 is not None:                                      # +neg at 2^(2i), -neg at 2^(2i+n+1)
            put(cols, [y2], 2 * i, +1, consts, width)
            put(cols, [y2], 2 * i + n + 1, -1, consts, width)
    # five-variable row bits become wires here; smaller ones stay atoms and are absorbed by counters
    for c in list(cols):
        out = []
        for a in cols[c]:
            if len(a[0]) > 3:
                vs, tt = a
                out.append(W(net.lut(list(vs), lambda bits, tt=tt: (tt >> sum(b << i for i, b in enumerate(bits))) & 1)))
            else:
                out.append(a)
        cols[c] = out
    return close(net, cols, consts, width)


def quad_leaf(net, X, Y):
    """Unsigned radix-4 rows: digit e = 2*y1 + y0 selects 0, X, 2X or T = 3X.  No sign wires."""
    n, m = len(X), len(Y)
    width = n + m
    cols = {}
    put(cols, X, 0, +1, [0], n + 2)
    put(cols, X, 1, +1, [0], n + 2)
    T = reduce_heap(net, cols, n + 2)
    cols = {}
    for i in range((m + 1) // 2):
        y0 = Y[2 * i]
        y1 = Y[2 * i + 1] if 2 * i + 1 < m else None
        for j in range(n + 2):
            xa = X[j] if j < n else None
            xb = X[j - 1] if 1 <= j <= n else None
            tj = T[j]
            parts = [a for a in (y0, y1, xa, xb, tj) if a is not None]
            vars_ = []
            for a in parts:
                for v in a[0]:
                    if v not in vars_:
                        vars_.append(v)

            def fn(bits, vars_=vars_, y0=y0, y1=y1, xa=xa, xb=xb, tj=tj):
                env = dict(zip(vars_, bits))
                g = lambda a: 0 if a is None else aval(a, env)
                e = g(y0) + 2 * g(y1)
                return (0, g(xa), g(xb), g(tj))[e]
            vals = [fn([(r >> t) & 1 for t in range(len(vars_))]) for r in range(1 << len(vars_))]
            c = 2 * i + j
            if c >= width or not any(vals):
                continue
            cols.setdefault(c, []).append((tuple(vars_), sum(v << r for r, v in enumerate(vals))))
    for c in list(cols):
        out = []
        for a in cols[c]:
            if len(a[0]) > 3:
                vs, tt = a
                out.append(W(net.lut(list(vs), lambda bits, tt=tt: (tt >> sum(b << i for i, b in enumerate(bits))) & 1)))
            else:
                out.append(a)
        cols[c] = out
    return close(net, cols, [0], width)


def best_of(net, builders):
    """Run each builder from the same state; keep the smallest."""
    mark = (len(net.luts), net.count, dict(net.level))
    best = None
    for b in builders:
        word = b()
        added = net.luts[mark[0]:]
        state = (word, added, net.count, {o: net.level[o] for o, _, _ in added})
        del net.luts[mark[0]:]
        net.count, net.level = mark[1], dict(mark[2])
        if best is None or len(added) < len(best[1]):
            best = state
    net.luts += best[1]
    net.count = best[2]
    net.level.update(best[3])
    return best[0]


class Wd(list):
    """A word: one atom (or None) per bit, with the block or input it is a slice of."""
    root, off = None, 0


def mk(atoms, root, off=0):
    w = Wd(atoms)
    w.root, w.off = root, off
    return w


def sl(w, lo, hi=None):
    hi = len(w) if hi is None else min(hi, len(w))
    return mk(list.__getitem__(w, slice(lo, hi)), w.root, w.off + lo)


def trim(w):
    n = len(w)
    while n and w[n - 1] is None:
        n -= 1
    return sl(w, 0, n)


def record(net, mark, out, width, operands, expr):
    """One derivation block: the LUTs made since mark compute out = expr(operands) mod 2^width."""
    bid = "b%d" % len(net.blocks)
    net.blocks.append({"id": bid, "width": width, "luts": [o for o, _, _ in net.luts[mark:]], "out": list(out),
                       "operands": [{"word": w.root, "lo": w.off, "hi": w.off + len(w)} for w in operands],
                       "expr": expr})
    return mk(list(out), bid)


def leaf_mult(net, X, Y):
    mark = len(net.luts)
    out = best_of(net, [lambda: booth_leaf(net, X, Y), lambda: booth_leaf(net, Y, X),
                        lambda: quad_leaf(net, X, Y), lambda: quad_leaf(net, Y, X)])
    return record(net, mark, out, len(X) + len(Y), [X, Y], [[1, [0, 1]]])


def add_words(net, A, B, width):
    mark = len(net.luts)
    cols = {}
    put(cols, A, 0, +1, [0], width)
    put(cols, B, 0, +1, [0], width)
    return record(net, mark, reduce_heap(net, cols, width), width, [A, B], [[1, [0]], [1, [1]]])


def square_leaf(net, X):
    """Folded square: x_i at 2^(2i), x_i x_j (i<j) at 2^(i+j+1)."""
    n = len(X)
    mark = len(net.luts)
    cols = {}
    for i in range(n):
        if X[i] is None:
            continue
        cols.setdefault(2 * i, []).append(X[i])
        for j in range(i + 1, n):
            if X[j] is not None:
                cols.setdefault(i + j + 1, []).append(((X[i][0][0], X[j][0][0]), 0b1000))
    return record(net, mark, close(net, cols, [0], 2 * n), 2 * n, [X], [[1, [0, 0]]])


DECIDE = {}


def _split(net, X, Y, sq, leaf):
    if sq:
        h = (len(X) + 1) // 2
        Xl, Xh = sl(X, 0, h), sl(X, h)
        z0 = mult(net, Xl, Xl, leaf)
        z2 = mult(net, Xh, Xh, leaf)
        sx = add_words(net, Xl, Xh, h + 1)
        p = mult(net, sx, sx, leaf)
        return _combine(net, z0, z2, p, h, 2 * len(X))
    h = (max(len(X), len(Y)) + 1) // 2
    Xl, Xh, Yl, Yh = sl(X, 0, h), sl(X, h), sl(Y, 0, h), sl(Y, h)
    z0 = mult(net, Xl, Yl, leaf)
    z2 = mult(net, Xh, Yh, leaf)
    sx = add_words(net, Xl, Xh, h + 1)
    sy = add_words(net, Yl, Yh, h + 1)
    p = mult(net, sx, sy, leaf)
    return _combine(net, z0, z2, p, h, len(X) + len(Y))


def mult(net, X, Y, leaf):
    """leaf > 0: split above that size.  leaf = 0: each size is built both ways once; the smaller is kept."""
    sq = X is Y or (X.root == Y.root and X.off == Y.off and len(X) == len(Y))
    X, Y = trim(X), trim(Y)
    assert X and Y
    as_leaf = lambda: square_leaf(net, X) if sq else leaf_mult(net, X, Y)
    lo, hi = min(len(X), len(Y)), max(len(X), len(Y))
    if leaf:
        return as_leaf() if lo <= leaf + 1 else _split(net, X, Y, sq, leaf)
    key = (len(X), len(Y), sq)
    if key not in DECIDE:
        if lo <= 10 or abs(len(X) - len(Y)) > 2:
            DECIDE[key] = "leaf"
        elif hi > 44:
            DECIDE[key] = "split"
        else:
            sizes = {}
            for name, fn in (("leaf", as_leaf), ("split", lambda: _split(net, X, Y, sq, leaf))):
                mark = (len(net.luts), net.count, dict(net.level), len(net.blocks))
                fn()
                sizes[name] = len(net.luts) - mark[0]
                del net.luts[mark[0]:]
                del net.blocks[mark[3]:]
                net.count, net.level = mark[1], mark[2]
            DECIDE[key] = min(sizes, key=sizes.get)
    return as_leaf() if DECIDE[key] == "leaf" else _split(net, X, Y, sq, leaf)


def _combine(net, z0, z2, p, h, width):
    dw = min(width - h, 2 * h + 2)                              # D = P - Z0 - Z2 >= 0
    zs = add_words(net, z0, z2, max(len(z0), len(z2)) + 1)
    mark = len(net.luts)
    cols, consts = {}, [0]
    put(cols, p, 0, +1, consts, dw)
    put(cols, zs, 0, -1, consts, dw)
    d = record(net, mark, close(net, cols, consts, dw), dw, [p, zs], [[1, [0]], [-1, [1]]])
    mark = len(net.luts)
    cols, consts = {}, [0]
    put(cols, z0, 0, +1, consts, width)
    put(cols, z2, 2 * h, +1, consts, width)
    put(cols, d, h, +1, consts, width)
    return record(net, mark, close(net, cols, consts, width), width, [z0, z2, d],
                  [[1, [0]], [1 << (2 * h), [1]], [1 << h, [2]]])


def compile_mul(n, leaf=16, square=False):
    net = Net()
    net.blocks = []
    A = mk([W("a[%d]" % i) for i in range(n)], "A")
    B = A if square else mk([W("b[%d]" % i) for i in range(n)], "B")
    word = mult(net, A, B, leaf)
    oname = "asquared" if square else "f"
    padded = list(word) + [None] * (2 * n - len(word))
    ren, made, seen = {}, [], set()
    for c, a in enumerate(padded):                              # outputs are named wires
        if a is not None and a != ONE and a[1] == 0b10 and a[0][0].startswith("n") and a[0][0] not in seen:
            ren[a[0][0]] = "%s[%d]" % (oname, c)
            seen.add(a[0][0])
        else:
            made.append((c, a))
    r = lambda v: ren.get(v, v)
    ra = lambda a: a if a is None or a == ONE else (tuple(r(v) for v in a[0]), a[1])
    net.luts = [(r(o), [r(v) for v in ins], tt) for o, ins, tt in net.luts]
    net.level = {r(v): l for v, l in net.level.items()}
    for b in net.blocks:
        b["luts"] = [r(o) for o in b["luts"]]
        b["out"] = [ra(a) for a in b["out"]]
    mark = len(net.luts)
    for c, a in made:
        a = ra(a)
        ins = [] if a is None else list(a[0])
        tt = sum((0 if a is None else aval(a, dict(zip(ins, [(q >> t) & 1 for t in range(len(ins))])))) << q
                 for q in range(1 << len(ins)))
        o = "%s[%d]" % (oname, c)
        net.count += 1
        net.luts.append((o, ins, tt))
        net.level[o] = 1 + max([net.level.get(v, 0) for v in ins] + [0])
    record(net, mark, [W("%s[%d]" % (oname, c)) for c in range(2 * n)], 2 * n, [mk(list(word), word.root)], [[1, [0]]])
    return net


def enc(a):
    if a is None:
        return None
    if a == ONE:
        return 1
    assert len(a[0]) == 1 and a[1] in (0b10, 0b01)
    return a[0][0] if a[1] == 0b10 else "!" + a[0][0]


def certificate(net, n, square, data):
    blocks = [dict(b, out=[enc(a) for a in b["out"]]) for b in net.blocks]
    return {"schema": SCHEMA, "n": n, "square": square, "k": net.k, "lut_count": len(net.luts),
            "levels": max(net.level.values()), "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest(),
            "contract": "sum 2^c out[c] = a*a" if square else "sum 2^c out[c] = a*b", "blocks": blocks}


def blif(net, n, square=False):
    ins = ["a[%d]" % i for i in range(n)] + ([] if square else ["b[%d]" % i for i in range(n)])
    oname = "asquared" if square else "f"
    L = [".model top", ".inputs " + " ".join(ins), ".outputs " + " ".join("%s[%d]" % (oname, i) for i in range(2 * n))]
    for o, vs, tt in net.luts:
        L.append(".names " + " ".join(vs + [o]))
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                L.append("".join("1" if (row >> i) & 1 else "0" for i in range(len(vs))) + " 1")
    L.append(".end")
    return ("\n".join(L) + "\n").encode()


def simulate(net, n, square=False, samples=2048, seed=1, exhaustive=False):
    """Bit-parallel check against integer multiplication."""
    if exhaustive:
        bits = n if square else 2 * n
        samples = 1 << bits
        vec = lambda i: sum(((s >> i) & 1) << s for s in range(samples))
        env = {"a[%d]" % i: vec(i) for i in range(n)}
        if not square:
            env.update({"b[%d]" % i: vec(n + i) for i in range(n)})
    else:
        rnd = random.Random(seed)
        env = {"a[%d]" % i: rnd.getrandbits(samples) for i in range(n)}
        if not square:
            env.update({"b[%d]" % i: rnd.getrandbits(samples) for i in range(n)})
    full = (1 << samples) - 1
    for o, vs, tt in net.luts:
        acc = 0
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                t = full
                for i, v in enumerate(vs):
                    t &= env[v] if (row >> i) & 1 else ~env[v] & full
                acc |= t
        env[o] = acc
    oname = "asquared" if square else "f"
    for s in range(samples) if samples <= 4096 else random.Random(2).sample(range(samples), 4096):
        a = sum(((env["a[%d]" % i] >> s) & 1) << i for i in range(n))
        b = a if square else sum(((env["b[%d]" % i] >> s) & 1) << i for i in range(n))
        got = sum(((env["%s[%d]" % (oname, i)] >> s) & 1) << i for i in range(2 * n))
        if got != a * b:
            return False
    return True


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--leaf", type=int, default=0)
    p.add_argument("--square", action="store_true")
    p.add_argument("--out", type=Path)
    a = p.parse_args()
    net = compile_mul(a.n, a.leaf, a.square)
    data = blif(net, a.n, a.square)
    ok = simulate(net, a.n, a.square, exhaustive=(a.n * (1 if a.square else 2) <= 16))
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / ("square.blif" if a.square else "multiplier.blif")).write_bytes(data)
        (a.out / (("square" if a.square else "multiplier") + ".derivation.json")).write_text(
            json.dumps(certificate(net, a.n, a.square, data), sort_keys=True) + "\n")
    print(json.dumps({"n": a.n, "leaf": a.leaf, "lut_count": len(net.luts), "levels": max(net.level.values()),
                      "simulation": ok, "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
