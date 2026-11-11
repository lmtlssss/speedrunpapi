"""Threshold-count compiler: n-input "at least T ones" as a k-LUT network.

Contract. For inputs x_0..x_{n-1} in {0,1}, the single output equals
[popcount(x) >= T].  Method (retained boundary state): add the constant
C = 2^m - T, so the answer is bit m of popcount(x) + C.  Only carries cross
a column cut; a column's own residue is never observed and is dropped.
Every node is a counter whose exact local identity is recorded in a
derivation that an independent checker replays (see
independent_threshold_checker.py).  Size model: one LUT per node, at most
k inputs per node.  No physical claim is made by this file.
"""
import argparse
import hashlib
import itertools
import json
from functools import lru_cache
from pathlib import Path

SCHEMA = "colony.lut-threshold.v1"


def digest(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


class Net:
    def __init__(self, n, threshold, k=6):
        if not (1 <= threshold <= n) or k < 3:
            raise ValueError("need 1 <= T <= n and k >= 3")
        self.n, self.T, self.k = n, threshold, k
        self.m = (max(threshold, n - threshold + 1) - 1).bit_length()   # least m: 2^m >= T, 2^m > n - T
        self.C = (1 << self.m) - threshold
        if n + self.C >= (1 << (self.m + 1)):
            raise ValueError("internal width error")
        self.luts = []        # (out, [ins], truth-table int over len(ins) inputs)
        self.nodes = []       # derivation records
        self.level = {}
        self.heap = {}        # column -> list of wires
        for i in range(n):
            w = "A[%d]" % i
            self.level[w] = 0
            self.heap.setdefault(0, []).append(w)
        self.const = {j: (self.C >> j) & 1 for j in range(self.m + 1)}
        self.count = 0

    def new(self):
        self.count += 1
        return "n%d" % self.count

    def counter(self, picks, low, keep_sum, floor=None):
        """picks: list of (wire, column), column >= low.  X = sum 2^(col-low) + add.
        floor = f: columns low..low+f-1 are cleared by this node; their constants are
        absorbed (add) and only digits d >= f of X are emitted (the residue X mod 2^f
        is never observed).  floor = 0: every digit is emitted (value-preserving)."""
        f = (0 if keep_sum else 1) if floor is None else floor
        ins = [w for w, _ in picks]
        wts = [1 << (c - low) for _, c in picks]
        if len(ins) > self.k:
            raise ValueError("fan-in")
        add = 0
        for j in range(f):
            add += self.const[low + j] << j
            self.const[low + j] = 0
        vmax = sum(wts) + add
        outs = []
        lvl = 1 + max(self.level[w] for w in ins)
        for d in range(f, vmax.bit_length()):
            col = low + d
            if col > self.m + (8 if f == 0 else 0):     # value-preserving nodes may carry a bound-only digit
                raise ValueError("overflow past result column")
            tt = 0
            for row in range(1 << len(ins)):
                x = add + sum(wts[i] for i in range(len(ins)) if (row >> i) & 1)
                if (x >> d) & 1:
                    tt |= 1 << row
            o = self.new()
            self.luts.append((o, ins, tt))
            self.level[o] = lvl
            if d == 0 and getattr(self, "fifo", False):
                self.heap.setdefault(col, []).insert(0, o)     # running residue stays at the head of the chain
            else:
                self.heap.setdefault(col, []).append(o)
            outs.append([o, d])
        self.nodes.append({"in": [[w, wt] for w, wt in zip(ins, wts)], "add": add,
                           "unit": low, "floor": f, "out": outs})
        return outs

    def take(self, col, cnt, earliest=True):
        lst = self.heap[col]
        if not getattr(self, "fifo", False):
            lst.sort(key=lambda w: self.level[w])
        got = lst[:cnt]
        del lst[:cnt]
        return [(w, col) for w in got]


@lru_cache(maxsize=None)
def tail_cost(heights, consts, k, top):
    """Exact minimum node count to finish a small heap. heights[i] = wires in column low+i."""
    heights = list(heights)
    consts = list(consts)
    while heights and heights[0] == 0 and consts[0] == 0 and len(heights) > 1:
        heights.pop(0); consts.pop(0); top -= 1
    if top == 0:                       # only the result column remains
        tot = heights[0]
        return (0, None) if tot <= 1 and True else ((tot + k - 2) // (k - 1), ("or",))
    total = sum(heights)
    if total <= k:
        return (1, ("final",))
    best = (10 ** 9, None)
    h0 = heights[0]
    if h0 == 0:                        # constant-only column: push carry of const (none) and continue
        return tail_cost(tuple(heights[1:]), tuple(consts[1:]), k, top - 1)
    for a in range(1, min(h0, k) + 1):
        clears = a == h0
        for b in range(0, min(heights[1] if len(heights) > 1 else 0, k - a) + 1):
            for c in range(0, min(heights[2] if len(heights) > 2 else 0, k - a - b) + 1):
                if not clears and (b or c):
                    continue
                add = consts[0] if clears else 0
                vmax = a + 2 * b + 4 * c + add
                nh = heights[:] + [0, 0, 0, 0]
                nc = consts[:] + [0, 0, 0, 0]
                nh[0] -= a; nh[1] -= b; nh[2] -= c
                cost = 0
                for d in range(0 if not clears else 1, vmax.bit_length()):
                    if d > top:
                        cost = None; break
                    nh[d] += 1; cost += 1
                if cost is None:
                    continue
                if not clears and a < 2:
                    continue
                if clears:
                    nc[0] = 0
                    if a == 1 and b == 0 and c == 0 and add == 0:
                        cost = 0; nh[1] -= 0
                        # a lone residue bit carries nothing: drop it
                        nh2 = heights[:] ; nh2[0] = 0
                        sub = tail_cost(tuple(nh2), tuple(nc[:len(heights)]), k, top)
                        if sub[0] < best[0]:
                            best = (sub[0], ("drop",))
                        continue
                while len(nh) > top + 1 and nh[-1] == 0:
                    nh.pop(); nc.pop()
                sub = tail_cost(tuple(nh[:top + 1]), tuple(nc[:top + 1]), k, top)
                if cost + sub[0] < best[0]:
                    best = (cost + sub[0], ("ctr", a, b, c, clears))
    return best


def block_binary(net, wires):
    """Value-preserving reduction of `wires` (column 0) to one wire per column:
    the binary popcount of the block.  Returns {column: wire}."""
    k = net.k
    local = {0: list(wires)}
    col = 0
    while col in local or any(c > col for c in local):
        ws = local.get(col, [])
        while len(ws) > 1:
            g = ws[:k]
            del ws[:k]
            outs = net.counter([(w, col) for w in g], col, True)
            for o, d in outs:
                net.heap[col + d].remove(o)
                if d == 0:
                    ws.insert(0, o)
                else:
                    local.setdefault(col + d, []).append(o)
        local[col] = ws
        col += 1
    return {c: ws[0] for c, ws in local.items() if ws}


def build(n, threshold, k=6, tail=26, blocks=None, fifo=True):
    net = Net(n, threshold, k)
    net.fifo = fifo            # chain order: every wire depends on an input prefix through a small state
    if blocks:
        hold = []
        for blk in blocks:
            names = ["A[%d]" % i for i in blk]
            for w in names:
                net.heap[0].remove(w)
            hold.append(block_binary(net, names))
        for res in hold:
            for c, w in res.items():
                net.heap.setdefault(c, []).append(w)
    return _finish_size(net, tail)


def _finish_size(net, tail=26):
    k = net.k
    m = net.m
    low = 0
    while True:
        while low < m and not net.heap.get(low) and net.const[low] == 0:
            low += 1
        if low >= m:
            break
        total = sum(len(net.heap.get(c, [])) for c in range(low, m + 1))
        if total <= tail:
            break
        col = net.heap.get(low, [])
        if len(col) > k:
            net.counter(net.take(low, k), low, True)
        elif len(col) == 0:
            net.const[low] and None
            # a column holding only its constant: constant < unit, no carry
            net.const[low] = 0
        elif len(col) == 1 and net.const[low] == 0:
            col.pop()
        else:
            net.counter(net.take(low, len(col)), low, False)
    # exact tail
    while True:
        while low < m and not net.heap.get(low) and net.const[low] == 0:
            low += 1
        if low >= m:
            break
        heights = tuple(len(net.heap.get(c, [])) for c in range(low, m + 1))
        consts = tuple(net.const[c] for c in range(low, m + 1))
        total = sum(heights)
        if total <= k:
            picks = [(w, c) for c in range(low, m + 1) for w in net.heap.get(c, [])]
            for c in range(low, m + 1):
                net.heap[c] = []
            final_node(net, picks, low)
            low = m
            break
        cost, mv = tail_cost(heights, consts, k, m - low)
        if mv[0] == "drop":
            net.heap[low].pop()
        elif mv[0] == "ctr":
            _, a, b, c, clears = mv
            picks = net.take(low, a) + (net.take(low + 1, b) if b else []) + (net.take(low + 2, c) if c else [])
            net.counter(picks, low, not clears)
        else:
            raise RuntimeError("tail move " + str(mv))
    while True:                         # result column and above: [X >= 1]; total < 2^(m+1) is a theorem
        picks = [(w, c) for c in sorted(net.heap) if c >= m for w in net.heap[c]]
        if len(picks) <= 1:
            break
        for w, c in picks[:k]:
            net.heap[c].remove(w)
        final_node(net, picks[:k], m)
    top = net.heap.get(m, [])
    if len(top) != 1:
        raise RuntimeError("no result wire")
    return net, top[0]


def _ctr(net, picks, low):
    """Value-preserving counter whose outputs are returned instead of queued in the global heap."""
    outs = net.counter(picks, low, True)
    for o, d in outs:
        net.heap[low + d].remove(o)
    return outs


def to_binary(net, heap):
    """Value-preserving reduction of a local heap {column: [wires]} to one wire per column."""
    heap = {c: list(ws) for c, ws in heap.items()}
    c = 0
    while heap and c <= max(heap):
        ws = heap.get(c, [])
        while len(ws) > 1:
            g = ws[:net.k]
            del ws[:net.k]
            for o, d in _ctr(net, [(w, c) for w in g], c):
                if d == 0:
                    ws.insert(0, o)
                else:
                    heap.setdefault(c + d, []).append(o)
        heap[c] = ws
        c += 1
    return {c: ws for c, ws in heap.items() if ws}


def _merge(net, a, b, policy):
    """Union of two block heaps, then local compression.  size: 6:3 whenever a column holds 6;
    lazy: 6:3 only when a column holds at least policy[1] wires (fewer levels, harder ABC steps)."""
    heap = {}
    for h in (a, b):
        for c, ws in h.items():
            heap.setdefault(c, []).extend(ws)
    k = net.k
    if policy[0] in ("size", "lazy"):
        c = 0
        while c <= max(heap):
            ws = heap.get(c, [])
            if policy[0] == "lazy":
                ws.sort(key=lambda w: net.level[w])
            while len(ws) >= (k if policy[0] == "size" else policy[1]):
                g = ws[:k]
                del ws[:k]
                for o, d in _ctr(net, [(w, c) for w in g], c):
                    heap.setdefault(c + d, []).append(o)
            c += 1
    else:
        raise ValueError("unknown tree policy: use 'size' or 'lazy:<threshold>'")
    return {c: ws for c, ws in heap.items() if ws}


def load_tree(tree):
    """Blocks are index lists, [lo, hi] ranges, or {"idx": [...]}."""
    def dec(b):
        if isinstance(b, dict):
            return list(b["idx"])
        if len(b) == 2 and b[1] - b[0] + 1 != 2:
            return list(range(b[0], b[1] + 1))
        return list(b)
    if tree.get("decoded"):
        return tree
    return {"decoded": True, "root": dec(tree["root"]),
            "split": [[dec(b), dec(l), dec(r)] for b, l, r in tree["split"]]}


def build_tree(n, threshold, tree, policy=("size",), cut=None, k=6, tail=26, beam=4000):
    """Hierarchical construction over a binary block tree {"root": [...], "split": [[block, left, right], ...]}.
    Blocks absent from `split` are leaves.  cut = h: blocks of tree height <= h keep the redundant
    (carry-save) form and are converted to binary at the cut; above the cut plain binary addition is used.
    cut = None: the redundant form is carried to the root and finished directly (the delivered circuit)."""
    net = Net(n, threshold, k)
    net.fifo = True
    tree = load_tree(tree)
    split = {tuple(b): (tuple(l), tuple(r)) for b, l, r in tree["split"]}
    height = {}

    def ht(b):
        if b not in height:
            height[b] = 0 if b not in split else 1 + max(ht(c) for c in split[b])
        return height[b]

    def redundant(b):
        if b not in split:
            names = ["A[%d]" % i for i in b]
            for w in names:
                net.heap[0].remove(w)
            return to_binary(net, {0: names})
        l, r = split[b]
        return _merge(net, redundant(l), redundant(r), policy)

    def binary(b):
        if cut is None or ht(b) <= cut:
            return to_binary(net, redundant(b))
        l, r = split[b]
        x, y = binary(l), binary(r)
        return to_binary(net, {c: x.get(c, []) + y.get(c, []) for c in set(x) | set(y)})

    import sys
    sys.setrecursionlimit(100000)
    root = tuple(tree["root"])
    res = redundant(root) if cut is None else binary(root)
    if any(net.heap.get(c) for c in net.heap):
        raise RuntimeError("inputs outside the tree")
    for c, ws in res.items():
        net.heap.setdefault(c, []).extend(ws)
    if policy[0] == "size" or cut is not None:
        return _finish_size(net, tail)
    return _finish_depth(net, beam)


def final_node(net, picks, low):
    """Single output: bit (m-low) and above of X, i.e. [X + const >= 2^(m-low)]."""
    ins = [w for w, _ in picks]
    wts = [1 << (c - low) for _, c in picks]
    add = sum(net.const[c] << (c - low) for c in range(low, net.m + 1))
    for c in range(low, net.m + 1):
        net.const[c] = 0
    lim = 1 << (net.m - low)
    tt = 0
    for row in range(1 << len(ins)):
        x = add + sum(wts[i] for i in range(len(ins)) if (row >> i) & 1)
        if x >= lim:
            tt |= 1 << row
    o = net.new()
    net.luts.append((o, ins, tt))
    net.level[o] = 1 + max(net.level[w] for w in ins)
    net.heap.setdefault(net.m, []).append(o)
    net.nodes.append({"in": [[w, wt] for w, wt in zip(ins, wts)], "add": add, "unit": low,
                      "floor": net.m - low, "out": [[o, net.m - low]], "final": True})


def _wallace_level(net, k):
    m = net.m
    cols = [c for c in range(m) if net.heap.get(c)]
    if not cols or sum(len(ws) for ws in net.heap.values()) <= k:
        return
    low = cols[0]
    snap = {c: list(net.heap[c]) for c in cols}
    for c in cols:
        ws = snap[c]
        groups = [ws[i:i + k] for i in range(0, len(ws), k)]
        for g in groups:
            clears = c == low and len(groups) == 1
            if len(g) == 1 and not clears:
                continue
            for w in g:
                net.heap[c].remove(w)
            if clears and len(g) == 1 and net.const[c] == 0:
                continue
            net.counter([(w, c) for w in g], c, not clears)


def _abstract_steps(state, k, m):
    """state = (heights tuple over columns 0..m, consts tuple).  Yield (cost, newstate, actions)."""
    h, cst = state
    cols = [c for c in range(m) if h[c]]
    if not cols:
        return
    low = cols[0]
    menus = []
    for c in cols:
        opts = [()]
        full, r = divmod(h[c], k)
        sizes = [k] * full
        if sizes:
            opts.append(tuple(sizes))
        if r >= 2:
            opts.append(tuple(sizes + [r]))
            if r >= 3 and full:
                pass
        if h[c] > k and h[c] % k and full >= 1:      # balanced split, e.g. 8 -> 4+4
            parts = full + 1
            q, e = divmod(h[c], parts)
            opts.append(tuple([q + 1] * e + [q] * (parts - e)))
        menus.append(opts)
    blocks = [0]
    tot = 0
    for f in range(1, 5):
        if low + f > m:
            break
        tot += h[low + f - 1]
        if 0 < tot <= k:
            blocks.append(f)
    orm = [False, True] if h[m] >= 2 else [False]
    for f in blocks:
        for choice in itertools.product(*[menus[i] if cols[i] >= low + f else [()] for i in range(len(cols))]):
            for do_or in orm:
                nh = list(h); nc = list(cst); cost = 0; acts = []; ok = True
                if f:
                    picks = [(c, h[c]) for c in range(low, low + f) if h[c]]
                    add = sum(cst[low + j] << j for j in range(f))
                    vmax = sum(cnt << (c - low) for c, cnt in picks) + add
                    if vmax.bit_length() - 1 + low > m:
                        continue
                    for c, cnt in picks:
                        nh[c] -= cnt
                    for j in range(f):
                        nc[low + j] = 0
                    for d in range(f, vmax.bit_length()):
                        nh[low + d] += 1; cost += 1
                    acts.append(("blk", low, f))
                for i, sizes in enumerate(choice):
                    c = cols[i]
                    for sz in sizes:
                        if sz < 2:
                            continue
                        if sz.bit_length() - 1 + c > m:
                            ok = False; break
                        nh[c] -= sz
                        for d in range(sz.bit_length()):
                            nh[c + d] += 1; cost += 1
                        acts.append(("ctr", c, sz))
                    if not ok:
                        break
                if not ok or (not acts and not do_or):
                    continue
                if do_or:
                    g = min(h[m], k)
                    nh[m] -= g - 1; cost += 1
                    acts.append(("or", g))
                yield cost, (tuple(nh), tuple(nc)), acts


def build_depth(n, threshold, k=6, wallace=4, beam=4000, max_levels=8):
    net = Net(n, threshold, k)
    m = net.m
    for _ in range(wallace):
        _wallace_level(net, k)
    return _finish_depth(net, beam, max_levels)


def _finish_depth(net, beam=4000, max_levels=8):
    k, m = net.k, net.m
    start = (tuple(len(net.heap.get(c, [])) for c in range(m + 1)), tuple(net.const[c] for c in range(m + 1)))
    frontier = {start: (0, [])}
    best = None
    for depth in range(max_levels + 1):
        done = [(c, a) for st, (c, a) in frontier.items() if sum(st[0]) <= k]
        if done:
            best = min(done, key=lambda t: t[0])
            break
        nxt = {}
        for st, (c0, a0) in frontier.items():
            for cost, ns, acts in _abstract_steps(st, k, m):
                if ns not in nxt or nxt[ns][0] > c0 + cost:
                    nxt[ns] = (c0 + cost, a0 + [acts])
        keep = sorted(nxt.items(), key=lambda kv: (sum(kv[0][0]), kv[1][0]))[:beam]
        frontier = dict(keep)
    if best is None:
        raise RuntimeError("no finish within max_levels")
    for acts in best[1]:
        todo = []
        for a in acts:                      # select wires first: a level is simultaneous
            if a[0] == "blk":
                _, low, f = a
                picks = [(w, c) for c in range(low, low + f) for w in net.heap.get(c, [])]
                for c in range(low, low + f):
                    net.heap[c] = []
                todo.append(("c", picks, low, f))
            elif a[0] == "ctr":
                _, c, sz = a
                ws = net.heap[c][:sz]; del net.heap[c][:sz]
                todo.append(("c", [(w, c) for w in ws], c, 0))
            else:
                ws = net.heap[m][:a[1]]; del net.heap[m][:a[1]]
                todo.append(("o", [(w, m) for w in ws]))
        for t in todo:
            if t[0] == "c":
                net.counter(t[1], t[2], None, floor=t[3])
            else:
                final_node(net, t[1], m)
    low = min(c for c in range(m + 1) if net.heap.get(c))
    picks = [(w, c) for c in range(low, m + 1) for w in net.heap.get(c, [])]
    for c in range(m + 1):
        net.heap[c] = []
    final_node(net, picks, low)
    return net, net.heap[m][0]


def blif(net, out, model="top"):
    lines = [".model " + model,
             ".inputs " + " ".join("A[%d]" % i for i in range(net.n)),
             ".outputs maj"]
    for o, ins, tt in net.luts:
        name = "maj" if o == out else o
        lines.append(".names " + " ".join(ins) + " " + name)
        for row in range(1 << len(ins)):
            if (tt >> row) & 1:
                lines.append("".join("1" if (row >> i) & 1 else "0" for i in range(len(ins))) + " 1")
    lines.append(".end")
    return ("\n".join(lines) + "\n").encode()


def compile_threshold(n, threshold, k=6, tail=26, objective="size", wallace=4, beam=4000, blocks=None,
                      tree=None, policy=("size",), cut=None):
    if tree is not None:
        net, out = build_tree(n, threshold, tree, policy, cut, k, tail, beam)
    elif objective == "size":
        net, out = build(n, threshold, k, tail, blocks)
    else:
        net, out = build_depth(n, threshold, k, wallace, beam)
    if out.startswith("A["):               # degenerate: the answer is an input; emit one buffer LUT
        net.heap[net.m].remove(out)
        final_node(net, [(out, net.m)], net.m)
        out = net.heap[net.m][0]
    data = blif(net, out)
    nodes = json.loads(json.dumps(net.nodes).replace('"%s"' % out, '"maj"'))
    cert = {"schema": SCHEMA, "contract": "output = [popcount(A) >= T] for all 2^n inputs",
            "n": n, "threshold": threshold, "k": k, "result_column": net.m, "constant": net.C,
            "lut_count": len(net.luts), "levels": net.level[out],
            "netlist_digest": digest(data), "nodes": nodes,
            "independent_verifier": "colony.lut-threshold-independent.v1"}
    return data, cert


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--threshold", type=int, required=True)
    p.add_argument("--k", type=int, default=6)
    p.add_argument("--tail", type=int, default=26)
    p.add_argument("--objective", choices=("size", "depth"), default="size")
    p.add_argument("--wallace", type=int, default=4)
    p.add_argument("--beam", type=int, default=4000)
    p.add_argument("--tree", type=Path, help="binary block tree (hierarchical build, ABC-chain verifiable)")
    p.add_argument("--policy", default="size", help="size | lazy:<threshold>")
    p.add_argument("--cut", type=int, help="emit the chain hybrid for this tree height")
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    pol = tuple([a.policy.split(":")[0]] + [int(x) for x in a.policy.split(":")[1:]])
    data, cert = compile_threshold(a.n, a.threshold, a.k, a.tail, a.objective, a.wallace, a.beam,
                                   tree=json.loads(a.tree.read_text()) if a.tree else None, policy=pol, cut=a.cut)
    a.out.mkdir(parents=True, exist_ok=True)
    (a.out / "threshold.blif").write_bytes(data)
    (a.out / "derivation.json").write_text(json.dumps(cert, sort_keys=True) + "\n")
    print(json.dumps({"lut_count": cert["lut_count"], "levels": cert["levels"],
                      "netlist_digest": cert["netlist_digest"]}, sort_keys=True))


if __name__ == "__main__":
    main()
