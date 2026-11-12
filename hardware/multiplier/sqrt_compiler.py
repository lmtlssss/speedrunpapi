"""Integer square root compiler: 2m-bit a -> m-bit floor(sqrt(a)) as a 6-LUT network.

Non-restoring digit recurrence.  Row k forms  r' = 4r + pair + 4(q xor not s) + 3  (mod 2^(k+2)),
where s is the sign of r: one expression for both the add and the subtract row.
Each row is one LUT per bit: the carry into a column is recovered from the previous column's
wires and its sum bit.  The top LUT of a row emits the root bit itself.
"""
import argparse
import hashlib
import json
import math
import random
from pathlib import Path

from mul_compiler import Net, W, NOT, ONE, aval


def chain(net, cols, width, top_inverted=False):
    """cols[c]: at most two atoms.  Returns one atom per column of the sum mod 2^width."""
    word, prev, prev_s, carry = [], [], None, False
    for c in range(width):
        atoms = list(cols.get(c, []))
        last = c == width - 1
        if not carry and len(atoms) <= 1 and (not atoms or len(atoms[0][0]) <= 1) and not (last and top_inverted):
            word.append(atoms[0] if atoms else None)
            prev, prev_s, carry = atoms, None, False
            continue
        vars_ = []
        for a in atoms + (prev if carry else []):
            for v in a[0]:
                if v not in vars_:
                    vars_.append(v)
        if carry and prev_s is not None:
            vars_.append(prev_s)
        assert len(vars_) <= net.k, (c, vars_)

        def fn(bits, atoms=atoms, prev=prev, prev_s=prev_s, carry=carry, vars_=vars_, inv=(last and top_inverted)):
            env = dict(zip(vars_, bits))
            cin = 0
            if carry:
                sp = sum(aval(a, env) for a in prev)
                vin = 0 if prev_s is None else (env[prev_s] ^ (sp & 1))
                cin = (sp + vin) >> 1
            return ((sum(aval(a, env) for a in atoms) + cin) & 1) ^ inv
        o = net.lut(vars_, fn)
        word.append(W(o))
        carry_next = (len(atoms) + (1 if carry else 0)) >= 2
        prev, prev_s, carry = atoms, (o if carry else None), carry_next
    return word


def sign_only(net, cols, width):
    """Root bit of the last row: not(top bit of the sum).  Only carries are built, several columns per LUT."""
    cin, c = None, 0
    while True:
        group, vars_ = [], ([cin] if cin else [])
        while c < width:
            vs = list(vars_)
            for a in cols.get(c, []):
                for v in a[0]:
                    if v not in vs:
                        vs.append(v)
            if len(vs) > net.k:
                break
            vars_ = vs
            group.append(c)
            c += 1
        assert group
        done = c == width

        def fn(bits, group=group, vars_=vars_, cin=cin, done=done):
            env = dict(zip(vars_, bits))
            t = env[cin] if cin else 0
            for i, col in enumerate(group):
                t += sum(aval(a, env) for a in cols.get(col, [])) << i
            if done:
                return ((t >> (len(group) - 1)) & 1) ^ 1
            return (t >> len(group)) & 1
        o = net.lut(vars_, fn)
        if done:
            return o
        cin = o


def xnor_atom(q, s):
    """q xor (not s) for single-wire atoms q (or None = 0) and s (or None = 0)."""
    if s is None:
        return ONE if q is None else (q[0], q[1] ^ 0b11)
    if q is None:
        return (s[0], s[1] ^ 0b11)
    vs = [q[0][0], s[0][0]]
    tt = 0
    for row in range(4):
        env = {vs[0]: row & 1, vs[1]: (row >> 1) & 1}
        if aval(q, env) ^ aval(s, env) ^ 1:
            tt |= 1 << row
    return (tuple(vs), tt)


def sqrt_rows(net, x, m, oname="asqrt"):
    """x: 2m atoms (wire, inverted wire, constant or None).  Adds the rows; returns the renaming to output names."""
    r, s, qit = [], None, []                         # r: atoms of the remainder; s: its sign; qit: root bits, first made first
    net.rows = []
    for k in range(1, m + 1):
        i = m - k
        w = k + 2
        mark = len(net.luts)
        cols = {0: [a for a in (x[2 * i], ONE) if a is not None], 1: [a for a in (x[2 * i + 1], ONE) if a is not None]}
        for c in range(2, w):
            col = []
            if c - 2 < len(r) and r[c - 2] is not None:
                col.append(r[c - 2])
            j = c - 2                                 # root bit index, least significant = most recent
            q = qit[k - 2 - j] if 0 <= k - 2 - j < len(qit) else None
            b = xnor_atom(q, s)
            if b is not None:
                col.append(b)
            cols[c] = col
        if k == m:                                    # the last remainder is never observed
            top = sign_only(net, cols, w)
            word = [None] * (w - 1) + [W(top)]
        else:
            word = chain(net, cols, w, top_inverted=True)
            top = word[-1][0][0]                      # this wire is the root bit: not sign(r')
        qit.append(W(top))
        s = NOT(top)
        r = word[:-1] + [s]
        net.rows.append({"k": k, "luts": [o for o, _, _ in net.luts[mark:]], "out": list(r)})
    ren = {qit[t][0][0]: "%s[%d]" % (oname, m - 1 - t) for t in range(m)}
    f = lambda v: ren.get(v, v)
    net.luts = [(f(o), [f(v) for v in ins], tt) for o, ins, tt in net.luts]
    net.level = {f(v): l for v, l in net.level.items()}
    fa = lambda a: a if a is None or a == ONE else (tuple(f(v) for v in a[0]), a[1])
    for row in net.rows:
        row["luts"] = [f(o) for o in row["luts"]]
        row["out"] = [fa(a) for a in row["out"]]


def certificate(net, m, data, kind="sqrt", blocks=None):
    from mul_compiler import enc
    cert = {"schema": "colony.lut-sqrt.v1", "kind": kind, "m": m, "k": net.k, "lut_count": len(net.luts),
            "levels": max(net.level.values()), "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest(),
            "rows": [dict(r, out=[enc(a) for a in r["out"]]) for r in net.rows]}
    if blocks is not None:
        cert["blocks"] = [dict(b, out=[enc(a) for a in b["out"]]) for b in blocks]
    return cert


def compile_sqrt(m):
    net = Net()
    sqrt_rows(net, [W("a[%d]" % i) for i in range(2 * m)], m)
    return net


def blif(net, m):
    L = [".model top", ".inputs " + " ".join("a[%d]" % i for i in range(2 * m)),
         ".outputs " + " ".join("asqrt[%d]" % i for i in range(m))]
    for o, vs, tt in net.luts:
        L.append(".names " + " ".join(vs + [o]))
        for row in range(1 << len(vs)):
            if (tt >> row) & 1:
                L.append("".join("1" if (row >> i) & 1 else "0" for i in range(len(vs))) + " 1")
    L.append(".end")
    return ("\n".join(L) + "\n").encode()


def simulate(net, m, samples=2048, seed=1, exhaustive=False):
    n = 2 * m
    if exhaustive:
        samples = 1 << n
        env = {"a[%d]" % i: sum(((s >> i) & 1) << s for s in range(samples)) for i in range(n)}
    else:
        rnd = random.Random(seed)
        env = {"a[%d]" % i: rnd.getrandbits(samples) for i in range(n)}
        for i in range(n):                            # include small, large and perfect-square-adjacent operands
            env["a[%d]" % i] |= ((1 << 64) - 1) if i >= n - 1 else 0
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
        if sum(((env["asqrt[%d]" % i] >> s) & 1) << i for i in range(m)) != math.isqrt(a):
            return False
    return True


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--m", type=int, required=True, help="root bits; the operand has 2m bits")
    p.add_argument("--out", type=Path)
    a = p.parse_args()
    net = compile_sqrt(a.m)
    data = blif(net, a.m)
    ok = simulate(net, a.m, exhaustive=a.m <= 8)
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / "sqrt.blif").write_bytes(data)
        (a.out / "sqrt.derivation.json").write_text(json.dumps(certificate(net, a.m, data), sort_keys=True) + "\n")
    print(json.dumps({"m": a.m, "lut_count": len(net.luts), "levels": max(net.level.values()), "simulation": ok,
                      "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}))
