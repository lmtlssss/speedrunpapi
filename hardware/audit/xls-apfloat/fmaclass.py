#!/usr/bin/env python3
"""Classify the fma mismatches of one format by the classes of the operands and of the two results.

usage: fmaclass.py VDIR E F OUTDIR
"""
import array
import collections
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import xref
import xrun

vdir, e, f, outdir = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
os.makedirs(outdir, exist_ok=True)
name = "fma_%d_%d" % (e, f)
F = xref.Fmt(e, f)
W = F.w
raw, tb, vvp = (os.path.join(outdir, name + x) for x in (".raw", ".tb.v", ".vvp"))
open(tb, "w").write(xrun.testbench(name, ["a", "b", "c"], [W, W, W], W, raw))
subprocess.run(["iverilog", "-g2012", "-o", vvp, tb, os.path.join(vdir, name + ".v")], check=True)
subprocess.run(["vvp", "-n", vvp], check=True, capture_output=True)
got = array.array("I")
got.frombytes(open(raw, "rb").read())
cls = lambda x: F.dec(x)[0]
tally = collections.Counter()
ex = {}
n = 1 << W
idx = 0
for a in range(n):
    for b in range(n):
        for c in range(n):
            g = got[idx]
            idx += 1
            want = xref.fma(F, a, b, c)
            if g in want:
                continue
            key = (cls(a), cls(b), cls(c), "/".join(sorted(cls(w) for w in want)), cls(g))
            tally[key] += 1
            ex.setdefault(key, "%x %x %x want %s got %x" % (a, b, c, "/".join("%x" % w for w in sorted(want)), g))
print("classes of a, b, c -> wanted class, got class: count, first case   (z zero, s subnormal, n normal, i infinity, q NaN)")
for k, v in sorted(tally.items(), key=lambda kv: -kv[1]):
    print("  %s %s %s -> want %-3s got %s  %8d   %s" % (k[0], k[1], k[2], k[3], k[4], v, ex[k]))
print("total wrong", sum(tally.values()))
for p in (raw, tb, vvp):
    os.remove(p)
