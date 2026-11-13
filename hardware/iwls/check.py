"""Checks the rules and the circuits in this folder against the contest truth tables, on every input.

usage: python3 check.py DIR        DIR holds ex280.truth ... ex299.truth

For each function it prints the inputs where the rule differs from the table, the size of the circuit, and
the inputs where the circuit differs from the table. The circuit is simulated on all 2^n inputs at once, one big integer per node.
The exit status is 1 when any count is not zero.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import rules


def read_aig(path):
    """Binary AIGER without latches: (number of inputs, output literals, list of (rhs0, rhs1) per AND)."""
    data = open(path, "rb").read()
    end = data.index(b"\n")
    tag, m, i, l, o, a = data[:end].split()
    assert tag == b"aig" and int(l) == 0, path
    i, o, a = int(i), int(o), int(a)
    pos = end + 1
    outs = []
    for _ in range(o):
        end = data.index(b"\n", pos)
        outs.append(int(data[pos:end]))
        pos = end + 1
    ands = []
    for k in range(a):
        deltas = []
        for _ in range(2):
            value = shift = 0
            while True:
                byte = data[pos]
                pos += 1
                value |= (byte & 127) << shift
                shift += 7
                if byte < 128:
                    break
            deltas.append(value)
        lhs = 2 * (i + k + 1)
        rhs0 = lhs - deltas[0]
        ands.append((rhs0, rhs0 - deltas[1]))
    return i, outs, ands


def simulate(path):
    """One integer per output: bit x is the output value on input word x."""
    n, outs, ands = read_aig(path)
    size = 1 << n
    ones = (1 << size) - 1
    node = [0]
    for k in range(n):                      # input k is 1 on the words x with bit k set
        block = ((1 << (1 << k)) - 1) << (1 << k)
        node.append(block * (ones // ((1 << (1 << (k + 1))) - 1)))
    lit = lambda v: node[v >> 1] ^ (ones if v & 1 else 0)
    for rhs0, rhs1 in ands:
        node.append(lit(rhs0) & lit(rhs1))
    return n, [lit(v) for v in outs], len(ands)


def main(folder):
    bad = 0
    for first, rule in rules.RULES:
        for e in range(first, first + 5):
            path = "%s/ex%d.truth" % (folder, e)
            rows = [r.strip() for r in open(path) if r.strip()]
            n, table = rules.load(path)
            by_rule = sum(1 for x in range(1 << n) if rule(x, n) != table[x])
            m, outs, size = simulate("%s/ex%d.aig" % (HERE, e))
            assert m == n and len(outs) == len(rows)
            diff = 0
            for row, got in zip(rows, outs):    # the first character of a row is the word 2^n - 1
                diff |= int(row, 2) ^ got
            by_circuit = bin(diff).count("1")
            bad += by_rule + by_circuit
            print("ex%d  n = %d  rule: %d of %d inputs differ   circuit, %d AND nodes: %d of %d inputs differ"
                  % (e, n, by_rule, 1 << n, size, by_circuit, 1 << n))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
