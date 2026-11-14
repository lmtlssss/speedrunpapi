#!/usr/bin/env python3
"""Simulate the Verilog that XLS generated for each wrapper on every input and compare with xref.py.

usage: xrun.py VDIR TOPS.txt OUTDIR [NAME_PREFIX ...] [-j JOBS]

Each module is simulated with Icarus Verilog over all values of its inputs (first port outermost) and its
outputs are written as 32-bit words. One line per module: calls, wrong, not judged, and the cases where
the reference accepts two outputs with which one the library chose. Wrong calls go to OUTDIR/NAME.bad.
"""
import array
import collections
import itertools
import multiprocessing
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import xref


def ports(what, n):
    if what.startswith("fromfixed"):
        return ["x"]
    if what == "ldexp":
        return ["a", "e"]
    return ["a", "b", "c"][:n]


def testbench(name, names, widths, wout, path):
    lines = ["`timescale 1ns/1ps", "module tb;"]
    for n, w in zip(names, widths):
        lines.append("  reg [%d:0] %s;" % (w - 1, n))
    lines.append("  wire [%d:0] out;" % (wout - 1))
    lines.append("  reg [31:0] word;")
    lines.append("  integer fd;")
    for i in range(len(names)):
        lines.append("  integer i%d;" % i)
    lines.append("  %s dut(%s, .out(out));" % (name, ", ".join(".%s(%s)" % (n, n) for n in names)))
    lines.append("  initial begin")
    lines.append('    fd = $fopen("%s", "wb");' % path)
    for i, w in enumerate(widths):
        lines.append("    for (i%d = 0; i%d < %d; i%d = i%d + 1) begin" % (i, i, 1 << w, i, i))
        lines.append("      %s = i%d;" % (names[i], i))
    lines.append("      #1;")
    lines.append("      word = out;")
    lines.append('      $fwrite(fd, "%u", word);')
    for _ in widths:
        lines.append("    end")
    lines.append("    $fclose(fd);")
    lines.append("    $finish;")
    lines.append("  end")
    lines.append("endmodule")
    return "\n".join(lines) + "\n"


def run(job):
    vdir, outdir, name, widths, wout, what = job
    names = ports(what[0], len(widths))
    raw = os.path.join(outdir, name + ".raw")
    tb = os.path.join(outdir, name + ".tb.v")
    vvp = os.path.join(outdir, name + ".vvp")
    open(tb, "w").write(testbench(name, names, widths, wout, raw))
    c = subprocess.run(["iverilog", "-g2012", "-o", vvp, tb, os.path.join(vdir, name + ".v")], capture_output=True, text=True)
    if c.returncode:
        return name, None, c.stderr[-400:]
    s = subprocess.run(["vvp", "-n", vvp], capture_output=True, text=True)
    if s.returncode:
        return name, None, s.stdout[-400:] + s.stderr[-400:]
    got = array.array("I")
    with open(raw, "rb") as f:
        got.frombytes(f.read())
    total = 1
    for w in widths:
        total <<= w
    if len(got) != total:
        return name, None, "expected %d results, read %d" % (total, len(got))
    wrong = unjudged = 0
    choice = collections.Counter()
    bad = []
    T = None
    if what[0] in ("up", "updaz"):
        T = xref.Fmt(int(what[3]), int(what[4]))
    for idx, args in enumerate(itertools.product(*[range(1 << w) for w in widths])):
        e = xref.expect(what, args)
        g = got[idx]
        if e is None:
            unjudged += 1
            continue
        if e == "nan":
            ok = T.is_nan(g)
            if ok and g != T.qnan:
                choice["a NaN other than the canonical one"] += 1
        else:
            ok = g in e
            if ok and len(e) == 2:
                choice["rounds to the smallest normal: " + ("zero" if (g & ((1 << (wout - 1)) - 1)) == 0 else "smallest normal")] += 1
        if not ok:
            wrong += 1
            if len(bad) < 2000:
                want = "nan" if e == "nan" else "/".join("%x" % v for v in sorted(e))
                bad.append("%s | want %s got %x" % (" ".join("%x" % a for a in args), want, g))
    if bad:
        open(os.path.join(outdir, name + ".bad"), "w").write("\n".join(bad) + "\n")
    for p in (raw, tb, vvp):
        os.remove(p)
    return name, (total, wrong, unjudged, dict(choice)), ""


def main():
    argv = sys.argv[1:]
    jobs_n = 6
    if "-j" in argv:
        i = argv.index("-j")
        jobs_n = int(argv[i + 1])
        del argv[i:i + 2]
    vdir, tops, outdir, prefixes = argv[0], argv[1], argv[2], argv[3:]
    os.makedirs(outdir, exist_ok=True)
    jobs = []
    for line in open(tops):
        f = line.split()
        if prefixes and not any(f[0].startswith(p) for p in prefixes):
            continue
        jobs.append((vdir, outdir, f[0], [int(x) for x in f[1].split(",")], int(f[2]), f[3:]))
    jobs.sort(key=lambda j: sum(j[3]))
    tot = collections.Counter()
    with multiprocessing.Pool(jobs_n) as pool:
        for name, res, err in pool.imap_unordered(run, jobs, chunksize=1):
            if res is None:
                print("%-28s FAILED %s" % (name, err.strip().replace("\n", " | ")[:300]), flush=True)
                continue
            total, wrong, unjudged, choice = res
            tot["calls"] += total
            tot["wrong"] += wrong
            tot["not judged"] += unjudged
            tot["modules"] += 1
            print("%-28s calls %9d  wrong %8d  not judged %6d  %s" % (name, total, wrong, unjudged, choice if choice else ""), flush=True)
    print("  ".join("%s %d" % kv for kv in sorted(tot.items())))


if __name__ == "__main__":
    main()
