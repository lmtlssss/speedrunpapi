"""Depth build of the n x n multiplier as a 6-LUT network.

Level 1: radix-4 recoded row bits.  Then simultaneous 6:3 counters halve the heap height per level.
Last: a radix-3 prefix adder over the two remaining rows (group generate/propagate, three groups per LUT).
"""
import argparse
import hashlib
import json
from pathlib import Path

import mul_compiler as M
from mul_compiler import W, ONE, aval


TIMED = True


def booth_cols(net, X, Y):
    n, m = len(X), len(Y)
    width = n + m
    cols, consts = {}, [0]
    yv = lambda i: Y[i] if 0 <= i < m else None
    for i in range(0, (m + 2) // 2 + 1):
        y0, y1, y2 = yv(2 * i - 1), yv(2 * i), yv(2 * i + 1)
        if y0 is None and y1 is None and y2 is None:
            continue
        ys = [y0, y1, y2]
        for j in range(n + 1):
            xa = X[j] if j < n else None
            xb = X[j - 1] if j >= 1 else None
            vars_ = []
            for a in ys + [xa, xb]:
                if a is not None and a[0][0] not in vars_:
                    vars_.append(a[0][0])

            def fn(bits, vars_=vars_, ys=ys, xa=xa, xb=xb):
                env = dict(zip(vars_, bits))
                g = lambda a: 0 if a is None else aval(a, env)
                d = g(ys[0]) + g(ys[1]) - 2 * g(ys[2])
                mj = g(xa) if abs(d) == 1 else (g(xb) if abs(d) == 2 else 0)
                return mj ^ g(ys[2])
            c = 2 * i + j
            vals = [fn([(r >> t) & 1 for t in range(len(vars_))]) for r in range(1 << len(vars_))]
            if c >= width or not any(vals):
                continue
            if len(vars_) == 1:
                cols.setdefault(c, []).append(((vars_[0],), sum(v << r for r, v in enumerate(vals))))
            else:
                cols.setdefault(c, []).append(W(net.lut(vars_, fn)))
        if y2 is not None:
            M.put(cols, [y2], 2 * i, +1, consts, width)
            M.put(cols, [y2], 2 * i + n + 1, -1, consts, width)
    return cols, consts, width


def fold_consts(cols, width, extra=0):
    k = extra
    for c in list(cols):
        ones = sum(1 for a in cols[c] if a == ONE)
        cols[c] = [a for a in cols[c] if a != ONE]
        k += ones << c
    k %= 1 << width
    for c in range(width):
        if (k >> c) & 1:
            cols.setdefault(c, []).append(ONE)


def wallace(net, cols, width):
    """Each pass is one LUT level.  Columns are cut to a common target height, counting the digits
    that the counters of lower columns send up, so no carry ripples into a later level."""
    lvl = lambda a: max([net.level.get(v, 0) for v in a[0]] + [0])
    fold_consts(cols, width)
    while max(len(v) for v in cols.values()) > 2:
        hmax = max(len(v) for v in cols.values())
        target = max(2, (hmax + 1) // 2)
        while True:                                        # plan first; raise the target if a column cannot meet it
            plan, inc, ok = {}, {}, True
            for c in range(width):
                h = len(cols.get(c, []))
                need = h + inc.get(c, 0) - target
                sizes = []
                left = h
                while need > 0 and left >= 2:
                    k = min(6, left, need + 1)
                    k = max(k, 2)
                    sizes.append(k)
                    left -= k
                    need -= k - 1
                    digits = k.bit_length()
                    for d in range(1, digits):
                        inc[c + d] = inc.get(c + d, 0) + 1
                if need > 0:
                    ok = False
                    break
                plan[c] = sizes
            if ok:
                break
            target += 1
        new = {}
        for c in range(width):
            items = sorted(cols.get(c, []), key=lambda a: (a != ONE, lvl(a)))
            for k in plan[c]:
                g, items = items[:k], items[k:]
                tmp = {}
                M.counter(net, tmp, [(a, c) for a in g], c)
                for cc, v in tmp.items():
                    if cc < width:
                        new.setdefault(cc, []).extend(v)
            new.setdefault(c, []).extend(items)
        cols = new
        fold_consts(cols, width)
    return cols


def prefix_add(net, cols, width, group=3):
    """cols[c]: at most two atoms.  Returns the sum word, one atom per column."""
    def cvars(c):
        return [v for a in cols.get(c, []) for v in a[0]]

    def csum(c, env):
        return sum(aval(a, env) for a in cols.get(c, []))
    ng = (width + group - 1) // group
    span = lambda k: range(k * group, min(width, (k + 1) * group))
    # group generate / propagate
    G, P = {}, {}
    for k in range(ng):
        vs = []
        for c in span(k):
            for v in cvars(c):
                if v not in vs:
                    vs.append(v)
        size = len(span(k))

        def tot(bits, k=k, vs=vs, cin=0):
            env = dict(zip(vs, bits))
            return sum(csum(c, env) << i for i, c in enumerate(span(k))) + cin
        gv = [tot([(r >> t) & 1 for t in range(len(vs))]) >> size for r in range(1 << len(vs))]
        pv = [(tot([(r >> t) & 1 for t in range(len(vs))], cin=1) >> size) & ~g for r, g in zip(range(1 << len(vs)), gv)]
        mk = lambda vals: (None if not any(vals) else (ONE if all(vals) else W(net.lut(vs, lambda bits, vals=vals: vals[sum(b << t for t, b in enumerate(bits))]))))
        G[(k, k)] = mk(gv)
        P[(k, k)] = mk(pv)
    # prefix: node (lo, hi) covers groups lo..hi; carry into group k is G[(0, k-1)]
    ev = lambda a, env: 0 if a is None else aval(a, env)
    done = {k: (k, k) for k in range(ng)}                 # per end group: current (lo, hi)
    step = 1
    near = lambda k: done[k][0] == 0 or done[done[k][0] - 1][0] == 0   # complete, or one combine away
    while not all(near(k) for k in range(ng)):
        nxt = {}
        for k in range(ng):
            lo, hi = done[k]
            if lo == 0:
                nxt[k] = (lo, hi)
                continue
            parts = [(lo, hi)]
            cur = lo
            for _ in range(2):
                if cur > 0:
                    l2, h2 = done[cur - 1]
                    parts.append((l2, h2))
                    cur = l2
            new_lo = parts[-1][0]
            gs = [G[p] for p in parts]
            ps = [P[p] for p in parts]
            vs = []
            need_p = new_lo > 0
            for i, p in enumerate(parts):
                for a in ([gs[i]] if True else []) + ([ps[i]] if (i < len(parts) - 1 or need_p) else []):
                    if a is not None and a != ONE and a[0][0] not in vs:
                        vs.append(a[0][0])

            def gfn(bits, gs=gs, ps=ps, vs=vs):
                env = dict(zip(vs, bits))
                carry = ev(gs[-1], env)                        # lowest part first
                for i in range(len(gs) - 2, -1, -1):
                    carry = ev(gs[i], env) | (ev(ps[i], env) & carry)
                return carry

            def pfn(bits, ps=ps, vs=vs):
                env = dict(zip(vs, bits))
                return int(all(ev(p, env) for p in ps))
            mk = lambda f: (lambda vals: None if not any(vals) else (ONE if all(vals) else W(net.lut(vs, f))))(
                [f([(r >> t) & 1 for t in range(len(vs))]) for r in range(1 << len(vs))])
            assert len(vs) <= net.k, vs
            G[(new_lo, hi)] = mk(gfn)
            P[(new_lo, hi)] = mk(pfn) if need_p else None
            nxt[k] = (new_lo, hi)
        done = nxt
    word = []
    for c in range(width):
        k, j = divmod(c, group)
        if k == 0:
            cparts = []
        else:
            lo, hi = done[k - 1]
            cparts = [G[(lo, hi)]] if lo == 0 else [G[(lo, hi)], P[(lo, hi)], G[done[lo - 1]]]
        cin_vars = []
        for a in cparts:
            if a is not None and a != ONE and a[0][0] not in cin_vars:
                cin_vars.append(a[0][0])

        def cin_val(env, cparts=cparts):
            if not cparts:
                return 0
            if len(cparts) == 1:
                return ev(cparts[0], env)
            return ev(cparts[0], env) | (ev(cparts[1], env) & ev(cparts[2], env))
        lower = [cc for cc in span(k) if cc < c]
        vs = []
        for cc in lower + [c]:
            for v in cvars(cc):
                if v not in vs:
                    vs.append(v)

        def sfn(env, carry, c=c, lower=lower):
            for cc in lower:
                carry = (csum(cc, env) + carry) >> 1
            return (csum(c, env) + carry) & 1
        if len(vs) + len(cin_vars) <= net.k:
            allv = vs + cin_vars

            def fn(bits, allv=allv, sfn=sfn, cin_val=cin_val):
                env = dict(zip(allv, bits))
                return sfn(env, cin_val(env))
            vals = [fn([(r >> t) & 1 for t in range(len(allv))]) for r in range(1 << len(allv))]
            if not any(vals):
                word.append(None)
            elif all(vals):
                word.append(ONE)
            elif len(allv) == 1 and vals == [0, 1]:
                word.append(W(allv[0]))
            else:
                word.append(W(net.lut(allv, fn)))
        else:                                              # conditional sums, selected by the carry
            q0 = net.lut(vs, lambda bits, vs=vs, sfn=sfn: sfn(dict(zip(vs, bits)), 0))
            q1 = net.lut(vs, lambda bits, vs=vs, sfn=sfn: sfn(dict(zip(vs, bits)), 1))
            allv = [q0, q1] + cin_vars

            def fn(bits, allv=allv, cin_val=cin_val):
                env = dict(zip(allv, bits))
                return env[allv[1]] if cin_val(env) else env[allv[0]]
            word.append(W(net.lut(allv, fn)))
    return word


def prefix_add_timed(net, cols, width, group=3):
    """Prefix adder whose tree follows the arrival levels of the columns: early columns are combined
    early, so the late columns see a ready carry.  Same node laws as prefix_add."""
    def cvars(c):
        return [v for a in cols.get(c, []) for v in a[0]]

    def csum(c, env):
        return sum(aval(a, env) for a in cols.get(c, []))
    ev = lambda a, env: 0 if a is None else aval(a, env)
    lv = lambda a: 0 if a is None or a == ONE else net.level.get(a[0][0], 0)
    ng = (width + group - 1) // group
    span = lambda k: range(k * group, min(width, (k + 1) * group))
    arr = [max([net.level.get(v, 0) for c in span(k) for v in cvars(c)] + [0]) for k in range(ng)]
    INF = 10 ** 9
    # interval levels
    I = [[INF] * ng for _ in range(ng)]
    plan = {}
    for k in range(ng):
        I[k][k] = arr[k] + 1
    for size in range(2, ng + 1):
        for l in range(0, ng - size + 1):
            r = l + size - 1
            best = (INF, None)
            for m in range(l, r):
                t = 1 + max(I[l][m], I[m + 1][r])
                if t < best[0]:
                    best = (t, [(m + 1, r), (l, m)])
            if size >= 3:
                # three parts: scan m2, keep the best m1 by monotone search
                for m1 in range(l, r - 1):
                    a_ = I[l][m1]
                    if a_ + 1 >= best[0]:
                        break
                    for m2 in range(m1 + 1, r):
                        t = 1 + max(a_, I[m1 + 1][m2], I[m2 + 1][r])
                        if t < best[0]:
                            best = (t, [(m2 + 1, r), (m1 + 1, m2), (l, m1)])
            I[l][r], plan[(l, r)] = best
    # complete prefixes
    C = [INF] * ng
    cplan = {}
    for k in range(ng):
        best = (I[0][k], ("interval",))
        for j in range(k):
            t = 1 + max(C[j], I[j + 1][k])
            if t < best[0]:
                best = (t, ("two", j))
            for m in range(j + 1, k):
                t = 1 + max(C[j], I[j + 1][m], I[m + 1][k])
                if t < best[0]:
                    best = (t, ("three", j, m))
        C[k], cplan[k] = best
    memo, cmemo = {}, {}

    def mk(vs, f):
        vals = [f([(r >> t) & 1 for t in range(len(vs))]) for r in range(1 << len(vs))]
        if not any(vals):
            return None
        if all(vals):
            return ONE
        return W(net.lut(vs, f))

    def base(k):
        vs = []
        for c in span(k):
            for v in cvars(c):
                if v not in vs:
                    vs.append(v)
        size = len(span(k))

        def tot(bits, cin):
            env = dict(zip(vs, bits))
            return sum(csum(c, env) << i for i, c in enumerate(span(k))) + cin
        g = mk(vs, lambda bits: tot(bits, 0) >> size)
        p_ = mk(vs, lambda bits: (tot(bits, 1) >> size) & ~(tot(bits, 0) >> size) & 1)
        return g, p_

    def combine(parts, need_p):
        """parts: (G, P) from high to low."""
        vs = []
        for i, (g, p_) in enumerate(parts):
            for a in [g] + ([p_] if (i < len(parts) - 1 or need_p) else []):
                if a is not None and a != ONE and a[0][0] not in vs:
                    vs.append(a[0][0])
        assert len(vs) <= net.k

        def gfn(bits):
            env = dict(zip(vs, bits))
            carry = ev(parts[-1][0], env)
            for g, p_ in reversed(parts[:-1]):
                carry = ev(g, env) | (ev(p_, env) & carry)
            return carry

        def pfn(bits):
            env = dict(zip(vs, bits))
            return int(all(ev(p_, env) for _, p_ in parts))
        return mk(vs, gfn), (mk(vs, pfn) if need_p else None)

    def node(l, r):
        if (l, r) not in memo:
            memo[(l, r)] = base(l) if l == r else combine([node(a, b) for a, b in plan[(l, r)]], True)
        return memo[(l, r)]

    def complete(k):
        if k not in cmemo:
            kind = cplan[k]
            if kind[0] == "interval":
                cmemo[k] = node(0, k)[0]
            elif kind[0] == "two":
                cmemo[k] = combine([node(kind[1] + 1, k), (complete(kind[1]), None)], False)[0]
            else:
                cmemo[k] = combine([node(kind[2] + 1, k), node(kind[1] + 1, kind[2]), (complete(kind[1]), None)], False)[0]
        return cmemo[k]
    word = []
    for c in range(width):
        k, j = divmod(c, group)
        lower = [cc for cc in span(k) if cc < c]
        vs = []
        for cc in lower + [c]:
            for v in cvars(cc):
                if v not in vs:
                    vs.append(v)
        local = max([net.level.get(v, 0) for v in vs] + [0])
        cparts = []
        if k > 0:
            direct = len(vs) + 1 <= net.k
            best = (max(local if direct else local + 1, C[k - 1]), None)
            for lo in range(1, k):
                if (len(vs) + 3 <= net.k) or True:
                    d2 = len(vs) + 3 <= net.k
                    t = max(local if d2 else local + 1, I[lo][k - 1], C[lo - 1])
                    if t < best[0]:
                        best = (t, lo)
            if best[1] is None:
                cparts = [complete(k - 1)]
            else:
                g, p_ = node(best[1], k - 1)
                cparts = [g, p_, complete(best[1] - 1)]
        cin_vars = []
        for a in cparts:
            if a is not None and a != ONE and a[0][0] not in cin_vars:
                cin_vars.append(a[0][0])

        def cin_val(env, cparts=cparts):
            if not cparts:
                return 0
            if len(cparts) == 1:
                return ev(cparts[0], env)
            return ev(cparts[0], env) | (ev(cparts[1], env) & ev(cparts[2], env))

        def sfn(env, carry, c=c, lower=lower):
            for cc in lower:
                carry = (csum(cc, env) + carry) >> 1
            return (csum(c, env) + carry) & 1
        if len(vs) + len(cin_vars) <= net.k:
            allv = vs + cin_vars

            def fn(bits, allv=allv, sfn=sfn, cin_val=cin_val):
                env = dict(zip(allv, bits))
                return sfn(env, cin_val(env))
            vals = [fn([(r >> t) & 1 for t in range(len(allv))]) for r in range(1 << len(allv))]
            if not any(vals):
                word.append(None)
            elif all(vals):
                word.append(ONE)
            elif len(allv) == 1 and vals == [0, 1]:
                word.append(W(allv[0]))
            else:
                word.append(W(net.lut(allv, fn)))
        else:
            q0 = net.lut(vs, lambda bits, vs=vs, sfn=sfn: sfn(dict(zip(vs, bits)), 0))
            q1 = net.lut(vs, lambda bits, vs=vs, sfn=sfn: sfn(dict(zip(vs, bits)), 1))
            allv = [q0, q1] + cin_vars

            def fn(bits, allv=allv, cin_val=cin_val):
                env = dict(zip(allv, bits))
                return env[allv[1]] if cin_val(env) else env[allv[0]]
            word.append(W(net.lut(allv, fn)))
    return word


def square_cols(net, X):
    """Folded square, level 1: three products per counter."""
    n = len(X)
    width = 2 * n
    raw = {}
    for i in range(n):
        raw.setdefault(2 * i, []).append(X[i])
        for j in range(i + 1, n):
            raw.setdefault(i + j + 1, []).append(((X[i][0][0], X[j][0][0]), 0b1000))
    cols = {}
    for c in sorted(raw):
        prods = [a for a in raw[c] if len(a[0]) > 1]
        cols.setdefault(c, []).extend(a for a in raw[c] if len(a[0]) == 1)
        while prods:
            g, prods = prods[:3], prods[3:]
            tmp = {}
            M.counter(net, tmp, [(a, c) for a in g], c)
            for cc, v in tmp.items():
                if cc < width:
                    cols.setdefault(cc, []).extend(v)
    return cols, [0], width


def finish(net, word, oname):
    ren, made, seen = {}, [], set()
    for c, a in enumerate(word):
        if a is not None and a != ONE and a[1] == 0b10 and a[0][0].startswith("n") and a[0][0] not in seen:
            ren[a[0][0]] = "%s[%d]" % (oname, c)
            seen.add(a[0][0])
        else:
            made.append((c, a))
    r = lambda v: ren.get(v, v)
    net.luts = [(r(o), [r(v) for v in ins], tt) for o, ins, tt in net.luts]
    net.level = {r(v): l for v, l in net.level.items()}
    for c, a in made:
        ins = [] if a is None or a == ONE else [r(v) for v in a[0]]
        tt = sum((0 if a is None else aval((tuple(ins), a[1]) if ins else a, dict(zip(ins, [(q >> t) & 1 for t in range(len(ins))])))) << q
                 for q in range(1 << len(ins)))
        net.luts.append(("%s[%d]" % (oname, c), ins, tt))
        net.level["%s[%d]" % (oname, c)] = 1 + max([net.level.get(v, 0) for v in ins] + [0])
    return ren


def _close(net, cols, width, oname, n, square):
    heap = [o for o, _, _ in net.luts]
    rows = {c: list(v) for c, v in cols.items() if v}
    net.rows_level = max(net.level.values())
    ren = finish(net, (prefix_add_timed if TIMED else prefix_add)(net, cols, width), oname)
    r = lambda v: ren.get(v, v)
    enc = lambda a: 1 if a == ONE else (r(a[0][0]) if a[1] == 0b10 else "!" + r(a[0][0]))
    net.cert = {"schema": "colony.lut-mul-depth.v1", "n": n, "square": square, "width": width,
                "heap": [r(o) for o in heap], "rows": [[enc(a) for a in rows.get(c, [])] for c in range(width)]}
    return net


def compile_square_depth(n):
    net = M.Net()
    cols, consts, width = square_cols(net, [W("a[%d]" % i) for i in range(n)])
    fold_consts(cols, width, consts[0])
    return _close(net, wallace(net, cols, width), width, "asquared", n, True)


def compile_mul_depth(n):
    net = M.Net()
    cols, consts, width = booth_cols(net, [W("a[%d]" % i) for i in range(n)], [W("b[%d]" % i) for i in range(n)])
    fold_consts(cols, width, consts[0])
    return _close(net, wallace(net, cols, width), width, "f", n, False)


def certificate(net, data):
    return dict(net.cert, k=net.k, lut_count=len(net.luts), levels=max(net.level.values()),
                netlist_digest="sha256:" + hashlib.sha256(data).hexdigest())


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--out", type=Path)
    p.add_argument("--square", action="store_true")
    a = p.parse_args()
    net = compile_square_depth(a.n) if a.square else compile_mul_depth(a.n)
    data = M.blif(net, a.n, a.square)
    ok = M.simulate(net, a.n, a.square, exhaustive=(a.n if a.square else 2 * a.n) <= 16)
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        name = "square_depth" if a.square else "multiplier_depth"
        (a.out / (name + ".blif")).write_bytes(data)
        (a.out / (name + ".derivation.json")).write_text(json.dumps(certificate(net, data), sort_keys=True) + "\n")
    print(json.dumps({"n": a.n, "lut_count": len(net.luts), "levels": max(net.level.values()), "levels_before_adder": net.rows_level,
                      "simulation": ok, "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
