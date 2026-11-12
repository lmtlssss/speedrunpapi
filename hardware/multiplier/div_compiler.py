"""Divider compiler: n-bit a, b -> quotient = floor(a / b), remainder = a mod b, as a 6-LUT network.
b = 0 gives quotient = 2^n - 1, remainder = a.

Non-restoring rows on a growing word.  Row j keeps the remainder mod 2^(j+1):
    r' = 2r + a_bit + (b xnor s) + (1 - s)        (mod 2^(j+1)),   s = [r < 0]
which is 2r + a_bit - b for s = 0 and 2r + a_bit + b for s = 1.  The true sign is
    s' = [b >= 2^j]  or  top bit of r'
because b >= 2^j exceeds every prefix of a seen so far, and b < 2^j bounds |r'| below 2^j.
Each bit of a row is one LUT; the carry into a column is recovered from the previous column.
"""
import argparse
import hashlib
import json
import random
from pathlib import Path

from mul_compiler import Net, W, NOT, ONE, aval
from sqrt_compiler import chain, xnor_atom


def and_atom(d, s):
    """d and s for single-wire atoms."""
    if d is None or s is None:
        return None
    vs = [d[0][0], s[0][0]]
    tt = 0
    for row in range(4):
        env = {vs[0]: row & 1, vs[1]: (row >> 1) & 1}
        if aval(d, env) & aval(s, env):
            tt |= 1 << row
    return (tuple(vs), tt)


def compile_div(n, stride=4):
    net = Net()
    a = [W("a[%d]" % i) for i in range(n)]
    b = [W("b[%d]" % i) for i in range(n)]
    # F[i] = [b >= 2^i] is a wire only at every stride-th index; the root LUTs read the bits between
    F = {}
    for i in range(((n - 1) // stride) * stride, 0, -stride):
        ins = [b[c][0][0] for c in range(i, min(i + stride, n))] + ([F[i + stride]] if i + stride in F else [])
        F[i] = net.lut(ins, lambda bits: int(any(bits)))
    r, s, q = [], None, {}
    rows = []
    for j in range(1, n + 1):
        w = j + 1
        mark = len(net.luts)
        cols = {}
        for c in range(w):
            col = []
            rc = a[n - j] if c == 0 else (r[c - 1] if c - 1 < len(r) else None)
            if rc is not None:
                col.append(rc)
            if c < n:
                col.append(xnor_atom(b[c], s))
            else:
                col.append(xnor_atom(None, s))
            if c == 0:
                col.append(ONE if s is None else (s[0], s[1] ^ 0b11))
            cols[c] = [x for x in col if x is not None]
        word = chain(net, cols, w)
        row_luts = [o for o, _, _ in net.luts[mark:]]
        top = word[-1]
        ins, i = [], j                                  # root bit: not(top or b_j or b_j+1 ... or F)
        while i < n and i not in F:
            ins.append(b[i][0][0])
            i += 1
        if i in F:
            ins.append(F[i])
        tv = list(top[0]) if top is not None and top != ONE else []
        qj = net.lut(tv + ins, lambda bits, top=top, tv=tv: int(not (
            (aval(top, dict(zip(tv, bits))) if top is not None else 0) or any(bits[len(tv):]))))
        q[j] = qj
        s = NOT(qj)
        r = word
        rows.append({"j": j, "luts": row_luts, "out": list(word)})
    cols = {c: [x for x in (r[c], and_atom(b[c], s)) if x is not None] for c in range(n)}
    mark = len(net.luts)
    rem = chain(net, cols, n)
    ren = {q[j]: "quotient[%d]" % (n - j) for j in q}
    made = []
    for c, x in enumerate(rem):
        if x is not None and x != ONE and x[1] == 0b10 and x[0][0].startswith("n") and x[0][0] not in ren:
            ren[x[0][0]] = "remainder[%d]" % c
        else:
            made.append((c, x))
    f = lambda v: ren.get(v, v)
    net.luts = [(f(o), [f(v) for v in ins], tt) for o, ins, tt in net.luts]
    net.level = {f(v): l for v, l in net.level.items()}
    for c, x in made:
        vs = [] if x is None or x == ONE else [f(v) for v in x[0]]
        tt = sum((0 if x is None else aval((tuple(vs), x[1]) if vs else x, dict(zip(vs, [(k >> t) & 1 for t in range(len(vs))])))) << k
                 for k in range(1 << len(vs)))
        net.luts.append(("remainder[%d]" % c, vs, tt))
        net.level["remainder[%d]" % c] = 1 + max([net.level.get(v, 0) for v in vs] + [0])
    from mul_compiler import enc
    fa = lambda x: x if x is None or x == ONE else (tuple(f(v) for v in x[0]), x[1])
    net.cert = {"flags": [{"i": i, "lut": f(F[i])} for i in sorted(F, reverse=True)],
                "rows": [{"j": r_["j"], "luts": [f(o) for o in r_["luts"]], "out": [enc(fa(x)) for x in r_["out"]]} for r_ in rows],
                "rem": [o for o, _, _ in net.luts[mark:]]}
    return net


def certificate(net, n, data):
    return dict(net.cert, schema="colony.lut-div.v1", n=n, k=net.k, lut_count=len(net.luts),
                levels=max(net.level.values()), netlist_digest="sha256:" + hashlib.sha256(data).hexdigest())


def blif(net, n):
    L = [".model top", ".inputs " + " ".join(["a[%d]" % i for i in range(n)] + ["b[%d]" % i for i in range(n)]),
         ".outputs " + " ".join(["quotient[%d]" % i for i in range(n)] + ["remainder[%d]" % i for i in range(n)])]
    for o, vs, tt in net.luts:
        L.append(".names " + " ".join(vs + [o]))
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                L.append("".join("1" if (row >> i) & 1 else "0" for i in range(len(vs))) + " 1")
    L.append(".end")
    return ("\n".join(L) + "\n").encode()


def simulate(net, n, samples=2048, seed=1, exhaustive=False):
    if exhaustive:
        samples = 1 << (2 * n)
        A = [s & ((1 << n) - 1) for s in range(samples)]
        B = [s >> n for s in range(samples)]
    else:
        rnd = random.Random(seed)
        A = [rnd.getrandbits(rnd.randrange(1, n + 1)) if s % 3 else rnd.getrandbits(n) for s in range(samples)]
        B = [rnd.getrandbits(rnd.randrange(1, n + 1)) if s % 5 else rnd.getrandbits(n) for s in range(samples)]
        B[0], A[1], B[2] = 0, 0, 1
        A[3] = B[3] = (1 << n) - 1
    env = {}
    for i in range(n):
        env["a[%d]" % i] = sum(((A[s] >> i) & 1) << s for s in range(samples))
        env["b[%d]" % i] = sum(((B[s] >> i) & 1) << s for s in range(samples))
    full = (1 << samples) - 1
    for o, vs, tt in net.luts:
        acc = 0
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                t = full
                for i, v in enumerate(vs):
                    t &= env[v] if (row >> i) & 1 else ~env[v] & full
                acc |= t
        env[o] = acc
    for s in range(samples):
        qv = sum(((env["quotient[%d]" % i] >> s) & 1) << i for i in range(n))
        rv = sum(((env["remainder[%d]" % i] >> s) & 1) << i for i in range(n))
        want = (A[s] // B[s], A[s] % B[s]) if B[s] else ((1 << n) - 1, A[s])
        if (qv, rv) != want:
            return False
    return True


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--out", type=Path)
    a = p.parse_args()
    net = compile_div(a.n)
    data = blif(net, a.n)
    ok = simulate(net, a.n, exhaustive=a.n <= 8)
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / "div.blif").write_bytes(data)
        (a.out / "div.derivation.json").write_text(json.dumps(certificate(net, a.n, data), sort_keys=True) + "\n")
    print(json.dumps({"n": a.n, "lut_count": len(net.luts), "levels": max(net.level.values()), "simulation": ok,
                      "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
