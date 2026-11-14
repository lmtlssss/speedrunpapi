#!/usr/bin/env python3
"""Add up the .json records of one or more output directories.

usage: agg.py DIR [DIR ...]          totals, the cases not judged by format and outcome, the status flags
"""
import collections
import glob
import json
import os
import sys

tot = collections.Counter()
nj = collections.Counter()
nj_ex = {}
fl = collections.Counter()
fl_ex = {}
by_kind = collections.Counter()
wrong = collections.Counter()
for d in sys.argv[1:]:
    for path in sorted(glob.glob(os.path.join(d, "*.json"))):
        r = json.load(open(path))
        parts = r["run"].split(".")
        fmt, kind = parts[0], parts[1]
        op = parts[2] if kind == "bin" else kind
        tot["runs"] += 1
        for k in ("total", "ok", "wrong", "signals", "flags_checked", "flags_tiny_after", "flags_tiny_before"):
            tot[k] += r[k]
        by_kind[(op, "total")] += r["total"]
        by_kind[(op, "wrong")] += r["wrong"]
        if r["wrong"]:
            wrong[(fmt, op)] += r["wrong"]
        for tag, outcome, n, ex in r["not_judged"]:
            nj[(fmt, op, tag, outcome)] += n
            nj_ex.setdefault((fmt, op, tag, outcome), r["run"] + ": " + ex)
            tot["not judged"] += n
        for key, n, ex in r["flags_other"]:
            fl[(fmt, op, key)] += n
            fl_ex.setdefault((fmt, op, key), r["run"] + ": " + ex)
print("  ".join("%s %d" % kv for kv in tot.items()))
print()
for op in sorted({k[0] for k in by_kind}):
    print("%-8s total %9d  wrong %d" % (op, by_kind[(op, "total")], by_kind[(op, "wrong")]))
print()
for k, v in sorted(wrong.items()):
    print("wrong  %-12s %-8s %d" % (k[0], k[1], v))
print()
print("not judged:")
for k, v in sorted(nj.items()):
    print("  %-12s %-8s %-40s -> %-28s %7d   %s" % (k[0], k[1], k[2], k[3], v, nj_ex[k]))
print()
print("status flags that match neither reading of underflow:")
for k, v in sorted(fl.items()):
    print("  %-12s %-8s %-28s %7d   %s" % (k[0], k[1], k[2], v, fl_ex[k]))
