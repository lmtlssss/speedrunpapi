"""EPFL round-robin arbiter as LUT-6: grant[i] = req[i] and (a token reaches i), tokens start at set priority bits,
travel upward, stop at the first request, and one that leaves position 127 re-enters at 0. anyGrant = OR of req.

    v[i]  = token reaching i when nothing re-enters:   v[0] = pri[0],  v[i] = pri[i] | (v[i-1] & ~req[i-1])
    w     = token leaving 127                           = v[127] & ~req[127]
    nr[i] = no request below i
    grant[i] = req[i] & (v[i] | (w & nr[i]))

v and nr exist as wires at the even positions only; a grant LUT at an odd position rebuilds its own from the pair below.
"""
import sys
N = 128
luts = []            # (output, inputs, function)

def lut(out, ins, fn):
    luts.append((out, ins, fn))
    return out

P = lambda i: "priority[%d]" % i
R = lambda i: "req[%d]" % i
V = {0: P(0)}
for j in range(2, N, 2):
    V[j] = lut("v%d" % j, [V[j - 2], R(j - 2), P(j - 1), R(j - 1), P(j)],
               lambda v, r0, p1, r1, p2: p2 | ((1 - r1) & (p1 | ((1 - r0) & v))))
w = lut("w", [V[N - 2], R(N - 2), P(N - 1), R(N - 1)], lambda v, r0, p1, r1: (1 - r1) & (p1 | ((1 - r0) & v)))
NR = {}
NR[2] = lut("nr2", [R(0), R(1)], lambda a, b: (1 - a) & (1 - b))
for j in range(4, N, 2):
    NR[j] = lut("nr%d" % j, [NR[j - 2], R(j - 2), R(j - 1)], lambda n, a, b: n & (1 - a) & (1 - b))
lut("anyGrant", [NR[N - 2], R(N - 2), R(N - 1)], lambda n, a, b: 1 - (n & (1 - a) & (1 - b)))
lut("grant[0]", [R(0), P(0), w], lambda r, p, w_: r & (p | w_))
lut("grant[1]", [R(1), P(1), R(0), P(0), w], lambda r1, p1, r0, p0, w_: r1 & (p1 | ((1 - r0) & (p0 | w_))))
for j in range(2, N, 2):
    lut("grant[%d]" % j, [R(j), V[j], w, NR[j]], lambda r, v, w_, n: r & (v | (w_ & n)))
    lut("grant[%d]" % (j + 1), [R(j + 1), P(j + 1), R(j), V[j], w, NR[j]],
        lambda r1, p1, r0, v, w_, n: r1 & (p1 | ((1 - r0) & (v | (w_ & n)))))

out = [".model top", ".inputs " + " ".join([P(i) for i in range(N)] + [R(i) for i in range(N)]),
       ".outputs " + " ".join(["grant[%d]" % i for i in range(N)] + ["anyGrant"])]
for o, ins, fn in luts:
    out.append(".names " + " ".join(ins + [o]))
    for row in range(1 << len(ins)):
        if fn(*[(row >> i) & 1 for i in range(len(ins))]):
            out.append("".join(str((row >> i) & 1) for i in range(len(ins))) + " 1")
out.append(".end")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
print("LUTs", len(luts))
