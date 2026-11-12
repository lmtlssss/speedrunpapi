"""Fold divider: n-bit a, b -> quotient, remainder as a 6-LUT network of low depth.
b = 0 gives quotient = 2^n - 1, remainder = a.

b is normalised (dn = b * 2^s, top bit set) and a table value M, read from the top bits of dn,
places D = M * dn just below a power of two:  eps = 2^P - D,  0 <= eps < 2^(P - g).
Because  T * 2^P = T * D + T * eps,  the top field T of the running value folds back as T * eps:
    W = T * 2^p + L   ->   W' = L + T * eps * 2^(p - P),      W - W' = T * D * 2^(p - P).
W stays in two rows; T is the pair of top fields, used as radix-4 digits of eps and 3 eps.  One fold is one
row of selected multiples and three counter levels and retires `b` quotient bits.
The same fields drive  R = a - Q * b  in a second heap, so after the last fold  0 <= R < 3 b  and the answer
is  Q + j, R - j b  for the j in {0, 1, 2} with 0 <= R - j b < b.
"""
import argparse
import hashlib
import json
from pathlib import Path

import div_compiler as DC
import fold_model as FM
import mul_compiler as M
import mul_depth as MD
from mul_compiler import ONE, W, aval


def inv(a):
    if a is None:
        return ONE
    if a == ONE:
        return None
    vs, tt = a
    return (vs, tt ^ ((1 << (1 << len(vs))) - 1))


class Build:
    def __init__(self):
        self.net, self.cache = M.Net(6), {}

    def mk(self, atoms, f):
        """One LUT over the wires of `atoms` computing f(values).  Constants and single wires build nothing."""
        vs = []
        for a in atoms:
            if a is None or a == ONE:
                continue
            for v in a[0]:
                if v not in vs:
                    vs.append(v)
        assert len(vs) <= 6, len(vs)
        tt = 0
        for r in range(1 << len(vs)):
            env = {v: (r >> i) & 1 for i, v in enumerate(vs)}
            if f([0 if a is None else aval(a, env) for a in atoms]) & 1:
                tt |= 1 << r
        i = 0
        while i < len(vs):                                  # drop wires the function does not read
            k = len(vs)
            if any(not (r >> i) & 1 and ((tt >> r) ^ (tt >> (r | 1 << i))) & 1 for r in range(1 << k)):
                i += 1
                continue
            nt = idx = 0
            for r in range(1 << k):
                if not (r >> i) & 1:
                    nt |= ((tt >> r) & 1) << idx
                    idx += 1
            tt = nt
            vs.pop(i)
        if not vs:
            return ONE if tt else None
        if len(vs) == 1:
            return ((vs[0],), tt)
        key = (tuple(vs), tt)
        if key not in self.cache:
            self.cache[key] = W(self.net.lut(vs, lambda bits, tt=tt: (tt >> sum(b << i for i, b in enumerate(bits))) & 1))
        return self.cache[key]

    def big(self, atoms, f):
        """Function of more than six wires: LUT leaves, then 4:1 selects."""
        if len(atoms) <= 6:
            return self.mk(atoms, f)
        lo, sel = atoms[:-2], atoms[-2:]
        subs = [self.big(lo, lambda bits, s=s: f(bits + [s & 1, s >> 1])) for s in range(4)]
        return self.mk(subs + sel, lambda v: v[v[4] | v[5] << 1])

    def anyof(self, atoms):
        atoms = [a for a in atoms if a is not None]
        if not atoms:
            return None
        while len(atoms) > 1:
            atoms = [self.mk(atoms[i:i + 6], lambda v: int(any(v))) for i in range(0, len(atoms), 6)]
        return atoms[0]

    def digits(self, blk, j):
        """Leading-zero count of a 4^j-bit block as base-4 digits, most significant first."""
        if j == 0:
            return []
        q = len(blk) // 4
        subs = [blk[(3 - i) * q:(4 - i) * q] for i in range(4)]
        nz = [self.anyof(sb) for sb in subs[:3]]
        first = lambda v: 0 if v[0] else 1 if v[1] else 2 if v[2] else 3
        d = (self.mk(nz, lambda v: first(v) & 1), self.mk(nz, lambda v: first(v) >> 1))
        lower = [self.digits(sb, j - 1) for sb in subs]
        out = [d]
        for t in range(j - 1):
            out.append(tuple(self.mk([lower[i][t][h] for i in range(4)] + list(d), lambda v: v[v[4] | v[5] << 1]) for h in (0, 1)))
        return out

    def rows(self, cols, T, X, X3, shift, width, neg=False):
        """Adds (or subtracts) T * X * 2^shift, T read as radix-4 digits selecting 0, X, 2X, 3X."""
        const = 0
        for j in range(0, len(T), 2):
            t0, t1 = T[j], T[j + 1] if j + 1 < len(T) else None
            if t0 is None and t1 is None:
                continue
            for k in range(len(X3)):
                c = shift + j + k
                if c >= width:
                    break
                xk = X[k] if k < len(X) else None
                xl = X[k - 1] if 1 <= k <= len(X) else None
                a = self.mk([t0, t1, xk, xl, X3[k]], lambda v: (0, v[2], v[3], v[4])[v[0] | v[1] << 1])
                if a is None:
                    continue
                if neg:
                    a = inv(a)
                    const -= 1 << c
                    if a is None:
                        continue
                cols.setdefault(c, []).append(a)
        return const


def enc(a):
    if a is None:
        return 0
    if a == ONE:
        return 1
    assert len(a[0]) == 1 and a[1] in (0b10, 0b01)
    return a[0][0] if a[1] == 0b10 else "!" + a[0][0]


def enc_rows(cols, width):
    return [[enc(x) for x in cols.get(c, [])] for c in range(width)]


GUARD = 6                                                  # spare columns: exact heaps drop no carry


def compile_div(n, b=8, rconst=None):
    if rconst is None:                                      # first pass measures the constant of the R heap
        rconst = compile_div(n, b, rconst=0).rconst
    pr = FM.params(n, b)
    g, t, m, k, P, npad = (pr[x] for x in ("g", "t", "m", "k", "P", "npad"))
    assert n >= t
    tab = FM.table(pr)
    B = Build()
    net = B.net
    a = [W("a[%d]" % i) for i in range(n)]
    d = [W("b[%d]" % i) for i in range(n)]
    lev = lambda atoms: max([net.level.get(v, 0) for x in atoms if x not in (None, ONE) for v in x[0]] + [0])
    marks, dv = {}, {}
    state = [0]

    def take():
        """LUTs built since the last call; the LUT cache is cleared so no block reads another block's LUT by reuse."""
        names = [o for o, _, _ in net.luts[state[0]:]]
        state[0] = len(net.luts)
        B.cache = {}
        return names

    def heap(cols, width, const=0):
        cols = {c: [q for q in v if q is not None] for c, v in cols.items() if c < width}
        MD.fold_consts(cols, width, const)
        if max([len(v) for v in cols.values()] + [0]) > 2:
            cols = MD.wallace(net, cols, width)
        cols = {c: v for c, v in cols.items() if v}
        return cols, {"luts": take(), "rows": enc_rows(cols, width), "width": width}

    def adder(cols, width, const=0):
        cols, h = heap(cols, width, const)
        word = MD.prefix_add_timed(net, cols, width)
        return word, {"heap": h, "luts": take(), "out": [enc(q) for q in word]}

    def triple(word):
        cols = {}
        for c, q in enumerate(word):
            cols.setdefault(c, []).append(q)
            cols.setdefault(c + 1, []).append(q)
        return adder(cols, len(word) + 2)

    def shift(word, digs, width):
        stages = []
        j = len(digs)
        for tt_, dg in enumerate(digs):
            step = 4 ** (j - 1 - tt_)
            gq = lambda c: word[c] if 0 <= c < len(word) else None
            word = [B.mk([gq(c), gq(c - step), gq(c - 2 * step), gq(c - 3 * step)] + list(dg), lambda v: v[v[4] | v[5] << 1])
                    for c in range(width)]
            stages.append([enc(q) for q in word])
        return word, {"luts": take(), "stages": stages}

    # normalise
    j = 1
    while 4 ** j < n:
        j += 1
    digs = B.digits([None] * (4 ** j - n) + d, j)
    dv["digits"] = {"luts": take(), "out": [[enc(q) for q in dg] for dg in digs]}
    d3, dv["d3"] = triple(d)
    a3, dv["a3"] = triple(a)
    dn, dv["dn"] = shift(d, digs, n)
    dn3, dv["dn3"] = shift(d3, digs, n + 2)
    x, dv["x"] = shift(a, digs, 2 * n - 1)
    x3, dv["x3"] = shift(a3, digs, 2 * n + 1)
    marks["normalised"] = lev(dn + dn3 + x + x3)
    # table
    ix = dn[n - t:n - 1]
    val = lambda bits: tab[(1 << (t - 1)) | sum(v << i for i, v in enumerate(bits))]
    Mw = [B.big(ix, lambda bits, q=q: (val(bits) >> q) & 1) for q in range(m)]
    M3 = [B.big(ix, lambda bits, q=q: (3 * val(bits) >> q) & 1) for q in range(m + 2)]
    dv["table"] = {"luts": take(), "M": [enc(q) for q in Mw], "M3": [enc(q) for q in M3]}
    marks["table"] = lev(Mw + M3)
    # eps = -M dn mod 2^(P-g),  3 eps = -3 M dn mod 2^(P-g+2)
    we = P - g
    cols = {}
    c0 = B.rows(cols, Mw, dn, dn3, 0, we, neg=True)
    eps, dv["eps"] = adder(cols, we, c0)
    cols = {}
    c0 = B.rows(cols, M3, dn, dn3, 0, we + 2, neg=True)
    eps3, dv["eps3"] = adder(cols, we + 2, c0)
    marks["eps"] = lev(eps + eps3)
    # X = M x, exact, two rows
    cols = {}
    B.rows(cols, Mw, x, x3, 0, 10 ** 9)
    cols, dv["X"] = heap(cols, P + n + GUARD)
    marks["X"] = lev([q for v in cols.values() for q in v])
    # folds, with R = a - Q b and Q in step
    wr = n + 2
    rcols = {c: [a[c]] for c in range(n)}
    rtotal = 0
    qcols = {}
    fw = b + 2
    dv["folds"], dv["R"] = [], []
    for i in range(k):
        p = P + npad - (i + 1) * b
        TS, TC, low = [None] * fw, [None] * fw, {}
        for c, v in cols.items():
            if c < p:
                low[c] = list(v)
            elif c - p < fw:                               # columns above the field are zero by the bound
                assert len(v) <= 2
                TS[c - p] = v[0]
                if len(v) > 1:
                    TC[c - p] = v[1]
        off = p - P
        marks["field %d" % i] = lev(TS + TC)
        for T in (TS, TC):
            rtotal += B.rows(rcols, T, d, d3, off, wr, neg=True)
            for q, bit in enumerate(T):
                if bit is not None and off + q < n:
                    qcols.setdefault(off + q, []).append(bit)
        rcols, info = heap(rcols, wr, rconst if i == 0 else 0)
        dv["R"].append(info)
        if i == k - 1:
            break
        for T in (TS, TC):
            B.rows(low, T, eps, eps3, off, 10 ** 9)
        cols, info = heap(low, p + 2 + GUARD)
        dv["folds"].append(info)
    marks["R rows"] = lev([q for v in rcols.values() for q in v])
    # R, R - b, R - 2b
    copy = lambda cs: {c: list(v) for c, v in cs.items()}
    fin = dv["final"] = {}
    R0, fin["R0"] = adder(copy(rcols), wr)
    c1 = copy(rcols)
    for c in range(n):
        c1.setdefault(c, []).append(inv(d[c]))
    R1, fin["R1"] = adder(c1, wr, (1 << wr) - (1 << n) + 1)
    c2 = copy(rcols)
    for c in range(n):
        c2.setdefault(c + 1, []).append(inv(d[c]))
    R2, fin["R2"] = adder(c2, wr, (1 << wr) - (1 << (n + 1)) + 2)
    n1, n2 = R1[wr - 1], R2[wr - 1]
    pick = lambda v: v[2] if not v[4] else (v[1] if not v[3] else v[0])
    Qv, fin["Q"] = [], []
    for add in (0, 1, 2):
        w_, info = adder(copy(qcols), n, add)
        Qv.append(w_)
        fin["Q"].append(info)
    nzd = B.anyof(d)
    fin["nz"] = {"luts": take(), "out": enc(nzd)}
    rem = [B.mk([R0[c], R1[c], R2[c], n1, n2], pick) for c in range(n)]
    quo = [B.mk([Qv[0][c], Qv[1][c], Qv[2][c], n1, n2, nzd], lambda v: pick(v) if v[5] else 1) for c in range(n)]
    net.marks, net.params, net.rconst = marks, pr, rtotal
    ren = dict(MD.finish(net, quo, "quotient"))
    for x_ in rem:
        assert x_ in (None, ONE) or x_[0][0] not in ren, "shared output wire"
    ren.update(MD.finish(net, rem, "remainder"))
    names = [o for o, _, _ in net.luts[state[0]:]]
    fin["select"] = {"luts": [ren.get(o, o) for o in names]}

    def rn(o):
        if isinstance(o, str):
            return "!" + ren.get(o[1:], o[1:]) if o.startswith("!") else ren.get(o, o)
        if isinstance(o, list):
            return [rn(q) for q in o]
        if isinstance(o, dict):
            return {key: rn(q) for key, q in o.items()}
        return o
    dv = rn(dv)
    # keep the logic the outputs read; the rest is kept in the derivation as definitions
    by = {o: (ins, tt) for o, ins, tt in net.luts}
    live, stack = set(), ["quotient[%d]" % c for c in range(n)] + ["remainder[%d]" % c for c in range(n)]
    while stack:
        o = stack.pop()
        if o in live or o not in by:
            continue
        live.add(o)
        stack += by[o][0]
    rows_of = lambda ins, tt: ["".join("1" if (r >> q) & 1 else "0" for q in range(len(ins))) for r in range(1 << len(ins)) if (tt >> r) & 1]
    dv["ghost"] = {o: [ins, rows_of(ins, tt)] for o, ins, tt in net.luts if o not in live}
    net.luts = [(o, ins, tt) for o, ins, tt in net.luts if o in live]
    net.level = {o: l for o, l in net.level.items() if o in live}
    net.cert = dv
    return net


def certificate(net, n, b, data):
    return dict(net.cert, schema="colony.lut-div-fold.v1", n=n, b=b, k=6, lut_count=len(net.luts),
                levels=max(net.level.values()), netlist_digest="sha256:" + hashlib.sha256(data).hexdigest())


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--b", type=int, default=8)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--samples", type=int, default=4096)
    args = ap.parse_args()
    net = compile_div(args.n, args.b)
    data = DC.blif(net, args.n)
    ok = DC.simulate(net, args.n, samples=args.samples, exhaustive=2 * args.n <= 20)
    if args.out:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "div_fold.blif").write_bytes(data)
        (args.out / "div_fold.derivation.json").write_text(json.dumps(certificate(net, args.n, args.b, data), sort_keys=True) + "\n")
    print(json.dumps({"n": args.n, "b": args.b, "lut_count": len(net.luts), "levels": max(net.level.values()),
                      "marks": net.marks, "simulation": ok, "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
