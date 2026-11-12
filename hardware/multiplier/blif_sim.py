"""Bit-parallel simulator for general BLIF (.names with don't-cares and off-set covers)."""
import random


def load(path):
    text = open(path).read().replace("\\\n", " ")
    ins, outs, nodes, cur = [], [], [], None
    for line in text.splitlines():
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] == ".inputs":
            ins += t[1:]
        elif t[0] == ".outputs":
            outs += t[1:]
        elif t[0] == ".names":
            cur = (t[-1], t[1:-1], [])
            nodes.append(cur)
        elif t[0].startswith("."):
            cur = None
        elif cur is not None:
            cur[2].append(t if len(t) == 2 else ["", t[0]])
    return ins, outs, nodes


def run(ins, outs, nodes, env, samples):
    full = (1 << samples) - 1
    pending = {o: (vs, rows) for o, vs, rows in nodes}
    order, seen = [], set(ins)
    stack = list(outs)
    while stack:                                   # iterative topological order
        o = stack[-1]
        if o in seen:
            stack.pop()
            continue
        need = [v for v in pending[o][0] if v not in seen]
        if need:
            stack += need
        else:
            seen.add(o)
            order.append(o)
            stack.pop()
    for o in order:
        vs, rows = pending[o]
        acc, pol = 0, "1"
        for cube, val in rows:
            pol = val
            t = full
            for v, ch in zip(vs, cube):
                if ch == "1":
                    t &= env[v]
                elif ch == "0":
                    t &= ~env[v] & full
            acc |= t
        env[o] = acc if pol == "1" else ~acc & full
    return env


def vectors(path, samples=256, seed=1):
    ins, outs, nodes = load(path)
    rnd = random.Random(seed)
    env = {w: rnd.getrandbits(samples) for w in ins}
    run(ins, outs, nodes, env, samples)
    return ins, outs, env
