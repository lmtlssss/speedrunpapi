"""Hypotenuse compiler: floor(sqrt((a*a + b*b) mod 2^(2n))) for n-bit a, b, as a 6-LUT network.

Two squarers (mul_compiler), one addition, and the square-root rows (sqrt_compiler)."""
import argparse
import hashlib
import json
import math
import random
from pathlib import Path

import mul_compiler as M
import sqrt_compiler as S


def compile_hyp(n):
    net = M.Net()
    net.blocks = []
    A = M.mk([M.W("a[%d]" % i) for i in range(n)], "A")
    B = M.mk([M.W("b[%d]" % i) for i in range(n)], "B")
    sa = M.mult(net, A, A, 0)
    sb = M.mult(net, B, B, 0)
    x = M.add_words(net, sa, sb, 2 * n)
    S.sqrt_rows(net, list(x), n, "hypotenuse")
    return net


def blif(net, n):
    L = [".model top", ".inputs " + " ".join(["a[%d]" % i for i in range(n)] + ["b[%d]" % i for i in range(n)]),
         ".outputs " + " ".join("hypotenuse[%d]" % i for i in range(n))]
    for o, vs, tt in net.luts:
        L.append(".names " + " ".join(vs + [o]))
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                L.append("".join("1" if (row >> i) & 1 else "0" for i in range(len(vs))) + " 1")
    L.append(".end")
    return ("\n".join(L) + "\n").encode()


def simulate(net, n, samples=1024, seed=1, exhaustive=False):
    if exhaustive:
        samples = 1 << (2 * n)
        env = {("a[%d]" % i if i < n else "b[%d]" % (i - n)): sum(((s >> i) & 1) << s for s in range(samples)) for i in range(2 * n)}
    else:
        rnd = random.Random(seed)
        env = {"%s[%d]" % (c, i): rnd.getrandbits(samples) for c in "ab" for i in range(n)}
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
        a = sum(((env["a[%d]" % i] >> s) & 1) << i for i in range(n))
        b = sum(((env["b[%d]" % i] >> s) & 1) << i for i in range(n))
        if sum(((env["hypotenuse[%d]" % i] >> s) & 1) << i for i in range(n)) != math.isqrt((a * a + b * b) % (1 << (2 * n))):
            return False
    return True


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--out", type=Path)
    a = p.parse_args()
    net = compile_hyp(a.n)
    data = blif(net, a.n)
    ok = simulate(net, a.n, exhaustive=a.n <= 8)
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / "hyp.blif").write_bytes(data)
        (a.out / "hyp.derivation.json").write_text(
            json.dumps(S.certificate(net, a.n, data, "hyp", net.blocks), sort_keys=True) + "\n")
    print(json.dumps({"n": a.n, "lut_count": len(net.luts), "levels": max(net.level.values()), "simulation": ok,
                      "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
