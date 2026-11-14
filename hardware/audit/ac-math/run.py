# usage: python3 run.py OUT_DIR [PARTS] [FIRST_INCLUDE_DIR]
# Generates the test files, compiles them in parallel against the two libraries, runs them, and checks every line.
# A configuration for which the library itself does not compile is recorded in OUT_DIR/nocompile.json with the
# compiler's first error for it, left out, and the rest is compiled again (up to four rounds).
# AC_TYPES and AC_MATH name the checkouts of hlslibs/ac_types and hlslibs/ac_math.
# FIRST_INCLUDE_DIR, when given, is searched before both (a directory holding patched headers).
import json
import os
import re
import subprocess
import sys
import time

here = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1]
parts = int(sys.argv[2]) if len(sys.argv) > 2 else 8
first = sys.argv[3] if len(sys.argv) > 3 else None
types, math = os.environ["AC_TYPES"], os.environ["AC_MATH"]
cxx = os.environ.get("CXX", "c++")
# CXXEXTRA: more compiler flags, for example -ftrivial-auto-var-init=pattern (clang), which fills every
# automatic variable that the source leaves unset, so that a read of one shows in the result
extra = os.environ.get("CXXEXTRA", "").split()
# ACM_MODULE: which sweep to run, acm (division and square root, the default) or acs (the shifts)
MODULE = os.environ.get("ACM_MODULE", "acm")
sys.path.insert(0, here)
inc = (["-I", first] if first else []) + ["-I", os.path.join(types, "include"), "-I", os.path.join(math, "include")]
os.makedirs(out, exist_ok=True)
skip_path = os.path.join(out, "nocompile.json")
why_path = os.path.join(out, "nocompile_why.json")
if os.path.exists(skip_path):
    os.remove(skip_path)
why = {}

for attempt in range(4):
    subprocess.run([sys.executable, os.path.join(here, MODULE + ".py"), "gen", out, str(parts)], check=True)
    t0 = time.time()
    procs = []
    for p in range(parts):
        src, exe = os.path.join(out, "t_%d.cpp" % p), os.path.join(out, "t_%d" % p)
        procs.append(subprocess.Popen([cxx, "-std=c++17", "-O1", "-w", "-ferror-limit=0", "-fno-caret-diagnostics"] + extra + inc + [src, "-o", exe],
                                      stderr=subprocess.PIPE, text=True))
    bad = set()
    for p in procs:
        err = p.communicate()[1]
        if p.returncode:
            # each error is followed by notes; the note that names the generated call carries the configuration id
            last_error = None
            for line in err.split("\n"):
                m = re.search(r"(ac_\w+\.h:\d+):\d+: error: (.*)", line)
                if m:
                    last_error = m.group(1) + ": " + m.group(2)[:150]
                m = re.search(r"(?:fdiv|fsqrt|idiv|isqrt_|shift_)<[^']*>' requested here", line)
                if m and last_error:
                    pass
                m = re.search(r"specialization '(fdiv|fsqrt|idiv|isqrt_|shift_)<([^']*)>' requested here", line)
                if m and last_error:
                    key = m.group(1) + "<" + m.group(2) + ">"
                    why.setdefault(key, last_error)
            bad.add(1)
    print("round %d: compiled %d files in %.0f s, %d distinct failing instantiations so far" % (attempt + 1, parts, time.time() - t0, len(why)))
    if not bad:
        break
    # map the failing instantiations back to configuration ids through the generated call text
    cs = json.load(open(os.path.join(out, "configs.json")))
    sys.path.insert(0, here)
    acm = __import__(MODULE)
    ids = []
    for c in cs:
        text = acm.call(c).strip()
        key = text[:text.rindex("(")]
        if key in why:
            ids.append(c["id"])
    json.dump(ids, open(skip_path, "w"))
    json.dump(why, open(why_path, "w"), indent=1)
else:
    raise SystemExit("still failing to compile after four rounds")

# Two runs: the output variables hold 0101... before each call in the first and 1010... in the second.
paths = []
for tag, sentinel in (("a", "55555555"), ("b", "aaaaaaaa")):
    res = os.path.join(out, "results_%s.txt" % tag)
    paths.append(res)
    with open(res, "wb") as f:
        runs = [subprocess.Popen([os.path.join(out, "t_%d" % p), sentinel], stdout=subprocess.PIPE) for p in range(parts)]
        for r in runs:
            f.write(r.communicate()[0])
            if r.returncode:
                raise SystemExit("a test program failed")
    print("== output variables hold %s before each call" % sentinel, flush=True)
    subprocess.run([sys.executable, os.path.join(here, MODULE + ".py"), "check", out, res, "1"], check=True)
print("== the two runs compared", flush=True)
subprocess.run([sys.executable, os.path.join(here, MODULE + ".py"), "depends", out, paths[0], paths[1], "6"], check=True)
