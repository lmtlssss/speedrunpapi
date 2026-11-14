#!/usr/bin/env python3
"""Run two harness binaries on the same jobs and compare their output line by line.

usage: diffbin.py APF_A APF_B FORMATS KINDS [JOBS]

Prints how many results are identical, how many differ in the status word only (and which status became
which), and how many differ in anything else. CONV_TARGETS as for apref.py.
"""
import collections
import multiprocessing
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import apref


def command(apf, job):
    _, _, fname, kind, args = job
    if kind == "bin":
        return [apf, "bin", fname, args[0], args[1]]
    return [apf, kind, fname] + list(args)


def run(task):
    a, b, job = task
    pa = subprocess.Popen(command(a, job), stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    pb = subprocess.Popen(command(b, job), stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    same = other = 0
    status = collections.Counter()
    example = {}
    for la, lb in zip(pa.stdout, pb.stdout):
        if la == lb:
            same += 1
            continue
        ga, gb = la.split("|")[1].split(), lb.split("|")[1].split()
        if len(ga) >= 3 and len(gb) >= 3 and ga[:2] == gb[:2] and ga[3:] == gb[3:] and "!" not in ga and "!" not in gb:
            key = "%s -> %s" % (ga[2], gb[2])
            status[key] += 1
            example.setdefault(key, ".".join([job[2], job[3]] + list(job[4])) + ": " + la.split("|")[0].strip())
        else:
            other += 1
            example.setdefault("other", ".".join([job[2], job[3]] + list(job[4])) + ": " + la.strip() + "  /  " + lb.strip())
    pa.wait()
    pb.wait()
    return same, other, status, example, job[3] if job[3] != "bin" else job[4][0]


def main():
    a, b, formats, kinds = sys.argv[1], sys.argv[2], sys.argv[3].split(","), sys.argv[4].split(",")
    njobs = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    targets = os.environ.get("CONV_TARGETS", "").split(",") if os.environ.get("CONV_TARGETS") else formats
    jobs = apref.jobs_for("", "", formats, kinds, targets)
    with multiprocessing.Pool(njobs) as pool:
        results = pool.map(run, [(a, b, j) for j in jobs], chunksize=1)
    same = other = 0
    status = collections.Counter()
    by_op = collections.Counter()
    example = {}
    for s, o, st, ex, op in results:
        same += s
        other += o
        status.update(st)
        by_op[op] += sum(st.values())
        for k, v in ex.items():
            example.setdefault(k, v)
    print("runs %d  identical %d  status only %d  anything else %d" % (len(results), same, sum(status.values()), other))
    for k, v in sorted(status.items()):
        print("  status %-10s %9d   %s" % (k, v, example[k]))
    for k, v in sorted(by_op.items()):
        if v:
            print("  %-8s %d" % (k, v))
    if other:
        print("  other: " + example["other"])


if __name__ == "__main__":
    main()
