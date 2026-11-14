# usage: python3 convrun.py OUT_DIR [PARTS] [FIRST_INCLUDE_DIR]
# Generates the conversion test files (acconv.py), compiles them in parallel, sets aside the configurations the
# library does not compile for, runs the rest and checks every line. AC_TYPES names the checkout of hlslibs/ac_types.
# FIRST_INCLUDE_DIR, when given, is searched first (a directory holding a patched header).
import json
import os
import re
import subprocess
import sys
import time

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import acconv

out = sys.argv[1]
parts = int(sys.argv[2]) if len(sys.argv) > 2 else 8
first = sys.argv[3] if len(sys.argv) > 3 else None
cxx = os.environ.get("CXX", "c++")
extra = os.environ.get("CXXEXTRA", "").split()
inc = (["-I", first] if first else []) + ["-I", os.path.join(os.environ["AC_TYPES"], "include")]
os.makedirs(out, exist_ok=True)
skip_path = os.path.join(out, "nocompile.json")
if os.path.exists(skip_path):
    os.remove(skip_path)
why = {}
for attempt in range(4):
    acconv.gen(out, parts)
    t0 = time.time()
    procs = [subprocess.Popen([cxx, "-std=c++17", "-O1", "-w", "-ferror-limit=0", "-fno-caret-diagnostics"] + extra + inc +
                              [os.path.join(out, "t_%d.cpp" % p), "-o", os.path.join(out, "t_%d" % p)],
                              stderr=subprocess.PIPE, text=True) for p in range(parts)]
    failed = False
    for p in procs:
        err = p.communicate()[1]
        if p.returncode:
            failed = True
            last = None
            for line in err.split("\n"):
                m = re.search(r"(ac_\w+\.h:\d+):\d+: error: (.*)", line)
                if m:
                    last = m.group(1) + ": " + m.group(2)[:150]
                m = re.search(r"specialization '(f2f|f2s|f2x|x2f)<([^']*)>' requested here", line)
                if m and last:
                    why.setdefault(m.group(1) + "<" + m.group(2) + ">", last)
    print("round %d: compiled in %.0f s, %d failing instantiations so far" % (attempt + 1, time.time() - t0, len(why)), flush=True)
    if not failed:
        break
    cs = json.load(open(os.path.join(out, "configs.json")))
    ids = []
    for c in cs:
        text = acconv.call(c).strip()
        if text[:text.rindex("(")] in why:
            ids.append(c["id"])
    json.dump(ids, open(skip_path, "w"))
    json.dump(why, open(os.path.join(out, "nocompile_why.json"), "w"), indent=1)
else:
    raise SystemExit("still failing to compile after four rounds")
res = os.path.join(out, "results.txt")
with open(res, "wb") as f:
    runs = [subprocess.Popen([os.path.join(out, "t_%d" % p)], stdout=subprocess.PIPE) for p in range(parts)]
    for r in runs:
        f.write(r.communicate()[0])
        if r.returncode:
            raise SystemExit("a test program failed")
acconv.check(out, res, 2)
