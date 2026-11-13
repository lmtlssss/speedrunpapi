"""Proves the netlist of this folder equal to the EPFL benchmark `arbiter` on every input.

usage: python3 check.py <random_control/arbiter.aig of lsils/benchmarks> [arbiter_size_2027.blif]

Both circuits are turned into reduced ordered binary decision diagrams with the variable order
priority[0], req[0], priority[1], req[1], ... For a fixed order the diagram of a function is unique, so two outputs
are the same function exactly when they end in the same node. Python only, no packages.
"""
import os
import sys

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
N = 128

# ---- decision diagrams: node 0 is false, node 1 is true, node k >= 2 is (variable, low child, high child)
nodes = [None, None]
unique = {}
level = [1 << 30, 1 << 30]


def mk(var, lo, hi):
    if lo == hi:
        return lo
    key = (var, lo, hi)
    n = unique.get(key)
    if n is None:
        n = len(nodes)
        nodes.append(key)
        level.append(var)
        unique[key] = n
    return n


ite_memo = {}


def ite(f, g, h):
    """if f then g else h"""
    if f == 1:
        return g
    if f == 0:
        return h
    if g == h:
        return g
    if g == 1 and h == 0:
        return f
    key = (f, g, h)
    r = ite_memo.get(key)
    if r is not None:
        return r
    v = min(level[f], level[g], level[h])
    f0, f1 = (nodes[f][1], nodes[f][2]) if level[f] == v else (f, f)
    g0, g1 = (nodes[g][1], nodes[g][2]) if level[g] == v else (g, g)
    h0, h1 = (nodes[h][1], nodes[h][2]) if level[h] == v else (h, h)
    r = mk(v, ite(f0, g0, h0), ite(f1, g1, h1))
    ite_memo[key] = r
    return r


def neg(f):
    return ite(f, 0, 1)


# ---- the benchmark: binary AIGER
def read_aig(path):
    data = open(path, "rb").read()
    end = data.index(b"\n")
    tag, m, i, l, o, a = data[:end].split()
    assert tag == b"aig" and int(l) == 0
    i, o, a = int(i), int(o), int(a)
    pos = end + 1
    outs = []
    for _ in range(o):
        end = data.index(b"\n", pos)
        outs.append(int(data[pos:end]))
        pos = end + 1
    ands = []
    for k in range(a):
        d = []
        for _ in range(2):
            value = shift = 0
            while True:
                byte = data[pos]
                pos += 1
                value |= (byte & 127) << shift
                shift += 7
                if byte < 128:
                    break
            d.append(value)
        lhs = 2 * (i + k + 1)
        ands.append((lhs - d[0], lhs - d[0] - d[1]))
    return i, outs, ands


def aig_outputs(path, inputs):
    n, outs, ands = read_aig(path)
    assert n == len(inputs)
    val = [0] + list(inputs)
    lit = lambda v: neg(val[v >> 1]) if v & 1 else val[v >> 1]
    for r0, r1 in ands:
        val.append(ite(lit(r0), lit(r1), 0))
    return [lit(v) for v in outs]


# ---- the netlist: BLIF, LUTs of at most six inputs
def blif_outputs(path, by_name):
    text = open(path).read().replace("\\\n", " ")
    sig = dict(by_name)
    outputs, luts, cur = [], [], None
    for line in text.split("\n"):
        tok = line.split()
        if not tok or tok[0].startswith("#"):
            continue
        if tok[0] == ".outputs":
            outputs += tok[1:]
        elif tok[0] == ".names":
            cur = (tok[-1], tok[1:-1], [])
            luts.append(cur)
        elif tok[0][0] != ".":
            cur[2].append(tok)
    pending = {o: (ins, rows) for o, ins, rows in luts}

    def value(name):
        if name in sig:
            return sig[name]
        ins, rows = pending[name]
        vals = [value(v) for v in ins]
        onset = 0
        offset = rows and rows[0][-1] == "0"
        for row in rows:
            pat = row[0] if len(row) == 2 else ""
            cube = 1
            for ch, v in zip(pat, vals):
                if ch == "1":
                    cube = ite(cube, v, 0)
                elif ch == "0":
                    cube = ite(cube, neg(v), 0)
            onset = ite(onset, 1, cube)
        sig[name] = neg(onset) if offset else onset
        return sig[name]

    return [value(o) for o in outputs], len(luts)


if __name__ == "__main__":
    netlist = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "arbiter_size_2027.blif")
    pri = [mk(2 * i, 0, 1) for i in range(N)]
    req = [mk(2 * i + 1, 0, 1) for i in range(N)]
    ref = aig_outputs(sys.argv[1], pri + req)                    # inputs: priority[0..127], then req[0..127]
    names = {"priority[%d]" % i: pri[i] for i in range(N)}
    names.update({"req[%d]" % i: req[i] for i in range(N)})
    got, count = blif_outputs(netlist, names)
    assert len(ref) == len(got) == N + 1
    differ = sum(1 for a, b in zip(ref, got) if a != b)
    print("netlist: %d LUTs. outputs: %d. decision diagram nodes built: %d" % (count, len(got), len(nodes)))
    print("outputs that differ from the benchmark: %d of %d" % (differ, len(got)))
    sys.exit(1 if differ else 0)
