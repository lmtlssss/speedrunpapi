"""Checks the formula and the netlist of this folder against the EPFL sin benchmark on all 2^24 inputs.

usage: python3 check.py SIN.AIG        SIN.AIG is arithmetic/sin.aig of https://github.com/lsils/benchmarks

The benchmark, the netlist and the formula are evaluated on every input word a (bit 0 is the first input).
Needs numpy. The exit status is 1 when anything differs.
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
N = 24
LOW = 16                                    # inputs simulated together: 2^16 words per pass


def read_aig(path):
    """Binary AIGER without latches: (inputs, output literals, [(rhs0, rhs1)] per AND node)."""
    data = open(path, "rb").read()
    end = data.index(b"\n")
    tag, m, i, l, o, a = data[:end].split()
    assert tag == b"aig" and int(l) == 0
    i, o, a = int(i), int(o), int(a)
    pos, outs, ands = end + 1, [], []
    for _ in range(o):
        end = data.index(b"\n", pos)
        outs.append(int(data[pos:end]))
        pos = end + 1
    for k in range(a):
        d = []
        for _ in range(2):
            v = s = 0
            while True:
                byte = data[pos]
                pos += 1
                v |= (byte & 127) << s
                s += 7
                if byte < 128:
                    break
            d.append(v)
        rhs0 = 2 * (i + k + 1) - d[0]
        ands.append((rhs0, rhs0 - d[1]))
    return i, outs, ands


def read_blif(path):
    """Single-output covers: (inputs, outputs, [(name, fanins, rows, polarity)] in file order)."""
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
            cur = [t[-1], t[1:-1], [], "1"]
            nodes.append(cur)
        elif t[0].startswith("."):
            cur = None
        elif cur is not None:
            cur[2].append(t[0] if len(t) == 2 else "")
            cur[3] = t[-1]
    done, order, pending = set(ins), [], nodes
    while pending:                           # topological order
        rest = []
        for nd in pending:
            if all(v in done for v in nd[1]):
                order.append(nd)
                done.add(nd[0])
            else:
                rest.append(nd)
        assert len(rest) < len(pending)
        pending = rest
    return ins, outs, order


def patterns():
    size = 1 << LOW
    ones = (1 << size) - 1
    low = []
    for k in range(LOW):
        block = ((1 << (1 << k)) - 1) << (1 << k)
        low.append(block * (ones // ((1 << (1 << (k + 1))) - 1)))
    return size, ones, low


def unpack(words, size):
    """List of bit vectors (one integer per output) -> uint32 array of output words."""
    out = np.zeros(size, dtype=np.uint32)
    for i, w in enumerate(words):
        bits = np.unpackbits(np.frombuffer(w.to_bytes(size // 8, "little"), dtype=np.uint8), bitorder="little")
        out |= bits.astype(np.uint32) << np.uint32(i)
    return out


def table_of_aig(path):
    n, outs, ands = read_aig(path)
    assert n == N
    size, ones, low = patterns()
    table = np.zeros(1 << N, dtype=np.uint32)
    for hi in range(1 << (N - LOW)):
        node = [0] + low + [ones if (hi >> k) & 1 else 0 for k in range(N - LOW)]
        for r0, r1 in ands:
            node.append((node[r0 >> 1] ^ (ones if r0 & 1 else 0)) & (node[r1 >> 1] ^ (ones if r1 & 1 else 0)))
        table[hi << LOW:(hi + 1) << LOW] = unpack([node[v >> 1] ^ (ones if v & 1 else 0) for v in outs], size)
    return table


def table_of_blif(path):
    ins, outs, order = read_blif(path)
    assert len(ins) == N
    size, ones, low = patterns()
    table = np.zeros(1 << N, dtype=np.uint32)
    for hi in range(1 << (N - LOW)):
        env = dict(zip(ins[:LOW], low))
        for k in range(LOW, N):
            env[ins[k]] = ones if (hi >> (k - LOW)) & 1 else 0
        for name, fanin, rows, pol in order:
            acc = 0
            for r in rows:
                term = ones
                for ch, w in zip(r, fanin):
                    if ch == "1":
                        term &= env[w]
                    elif ch == "0":
                        term &= env[w] ^ ones
                acc |= term
            env[name] = acc if pol == "1" else acc ^ ones
        table[hi << LOW:(hi + 1) << LOW] = unpack([env[o] for o in outs], size)
    return table, len(order), max(len(nd[1]) for nd in order)


def table_of_formula(tables):
    C0, C1, K = (np.array(tables[k], dtype=np.int64) for k in ("C0", "C1", "K"))
    a = np.arange(1 << N, dtype=np.int64)
    q, b = a >> 22, a & ((1 << 22) - 1)
    y = np.where(q & 1, b, (-b) & ((1 << 22) - 1))
    A, Z = y >> 15, y & 32767
    core = ((C0[A] << 14) + (C1[A] - ((K[A] * (Z >> 3)) >> 12)) * Z + (1 << 16)) >> 17
    core = np.where(((q & 1) == 0) & (b == 0), 1 << 23, core)
    out = np.where((q == 0) | (q == 3), core, -core)
    return (out & ((1 << 25) - 1)).astype(np.uint32)


if __name__ == "__main__":
    ref = table_of_aig(sys.argv[1])
    formula = table_of_formula(json.load(open(HERE + "/tables.json")))
    d1 = int((formula != ref).sum())
    print("formula: %d of %d inputs differ from the benchmark" % (d1, 1 << N))
    net, nodes, fanin = table_of_blif(HERE + "/sin_size_2027.blif")
    d2 = int((net != ref).sum())
    print("netlist: %d nodes, at most %d inputs each, %d of %d inputs differ from the benchmark" % (nodes, fanin, d2, 1 << N))
    exact = np.rint((1 << 23) * np.cos(2 * np.pi * np.arange(1 << N) / (1 << N))).astype(np.int64)
    signed = np.where(ref >= (1 << 24), ref.astype(np.int64) - (1 << 25), ref.astype(np.int64))
    print("benchmark against the cosine rounded to nearest: equal on %d inputs, one off on %d, further off on %d"
          % (int((signed == exact).sum()), int((np.abs(signed - exact) == 1).sum()), int((np.abs(signed - exact) > 1).sum())))
    sys.exit(1 if d1 or d2 else 0)
