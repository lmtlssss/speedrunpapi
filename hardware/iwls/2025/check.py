"""Checks the rules of minifloat.py and half.py and the circuits in this folder against the IWLS 2025 truth tables,
on every input.

usage: python3 check.py DIR        DIR holds ex160.truth ... ex185.truth from
                                   https://github.com/alanminko/iwls2025-ls-contest (benchmarks/2025)

For each function it prints the inputs where the rule differs from the table. For each exNNN.aig in this folder it
prints the size of the circuit and the inputs where the circuit differs from the table.
The exit status is 1 when any count is not zero.
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import half
import minifloat

_spec = importlib.util.spec_from_file_location("iwls_check", os.path.join(os.path.dirname(HERE), "check.py"))
_parent = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_parent)
simulate = _parent.simulate           # the AIGER reader and simulator of the folder above


def table(path):
    """-> (n, rows, vals): rows are the output rows as written, vals[x] is the output word on input word x."""
    rows = [r.strip() for r in open(path) if r.strip()]
    n = len(rows[0]).bit_length() - 1
    size = 1 << n
    vals = [0] * size
    for j, row in enumerate(rows):          # the first character of a row is the input word 2^n - 1
        for p, ch in enumerate(row):
            if ch == "1":
                vals[size - 1 - p] |= 1 << j
    return n, rows, vals


def describe(ex):
    if ex < 180:
        name, eb, mb, _ = minifloat.function(ex)
        return "%-5s 1-%d-%d" % (name, eb, mb), minifloat.value
    return "%-5s half " % half.NAMES[ex], half.value


def main(folder):
    bad = 0
    for ex in range(160, 186):
        n, rows, vals = table("%s/ex%d.truth" % (folder, ex))
        label, rule = describe(ex)
        by_rule = sum(1 for u in range(1 << n) if rule(ex, u) != vals[u])
        line = "ex%d  %s  rule: %d of %d inputs differ" % (ex, label, by_rule, 1 << n)
        aig = "%s/ex%d.aig" % (HERE, ex)
        by_circuit = 0
        if os.path.exists(aig):
            m, outs, size = simulate(aig)
            assert m == n and len(outs) == len(rows)
            diff = 0
            for row, got in zip(rows, outs):
                diff |= int(row, 2) ^ got
            by_circuit = bin(diff).count("1")
            line += "   circuit, %d AND nodes: %d of %d inputs differ" % (size, by_circuit, 1 << n)
        bad += by_rule + by_circuit
        print(line, flush=True)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
