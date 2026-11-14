# usage: qtest | python3 acq.py
# Checks the quantization and overflow definitions of acm.py against the library's own ac_fixed assignment.
import sys
from fractions import Fraction

import acm

wrong = total = 0
per = {}
for line in sys.stdin:
    q, o, s, v, got = line.split()
    mode, omode, s = acm.QMODES[int(q)], acm.OMODES[int(o)], int(s)
    x = Fraction(acm.signed(int(v, 16), 7), 8)
    want = acm.overflow(acm.quantize(x, mode), 3, s, omode)
    total += 1
    if want != int(got, 16):
        wrong += 1
        key = (mode, omode, s)
        per[key] = per.get(key, 0) + 1
        if per[key] <= 2:
            print("  %s %s %s: %s -> %s, acm.py says %d" % (mode, omode, "signed" if s else "unsigned", x, got, want))
print("%d assignments, %d differ from the definitions in acm.py" % (total, wrong))
for k in sorted(per):
    print("  ", k, per[k])
