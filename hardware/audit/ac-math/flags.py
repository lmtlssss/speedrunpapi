# usage: python3 flags.py OUT_DIR RESULTS.txt   -> the calls whose returned flag is not "the remainder is nonzero"
import json
import os
import sys

import acm

cs = json.load(open(os.path.join(sys.argv[1], "configs.json")))
n = 0
per = {}
for line in open(sys.argv[2]):
    f = line.split()
    if "A" in f:
        continue
    c = cs[int(f[0])]
    want, got, flag = acm.expected(c, f)
    if flag is not None and flag[0] != flag[1]:
        n += 1
        per[acm.describe(c)] = per.get(acm.describe(c), 0) + 1
        if n <= 6:
            print("  %s: operands %s -> %s, the remainder is %s" % (acm.describe(c), " ".join(f[1:3]), " ".join(f[3:]), "nonzero" if flag[0] else "zero"))
print(n, "calls")
for k in sorted(per):
    print("  %4d  %s" % (per[k], k))
