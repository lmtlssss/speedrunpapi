"""Compiler and independent checker: exhaustive at small widths, replay at every width, tamper rejection."""
import hashlib
import mul_compiler as M
import independent_mul_checker as C


def build(n, leaf, square):
    net = M.compile_mul(n, leaf, square)
    data = M.blif(net, n, square)
    return net, data, M.certificate(net, n, square, data)


def truth(data, n):
    ins, outs, tables = C.parse_blif(data)
    S = 1 << (2 * n)
    full = (1 << S) - 1
    env = {w: sum(((s >> i) & 1) << s for s in range(S)) for i, w in enumerate(ins)}
    for o, (vs, onset) in tables.items():
        acc = 0
        for row in onset:
            t = full
            for v, ch in zip(vs, row):
                t &= env[v] if ch == "1" else ~env[v] & full
            acc |= t
        env[o] = acc
    for s in range(S):
        a, b = s & ((1 << n) - 1), s >> n
        if sum(((env[o] >> s) & 1) << i for i, o in enumerate(outs)) != a * b:
            return False
    return True


def main():
    for n, leaf, square in [(4, 0, False), (5, 2, False), (7, 2, False), (8, 3, False), (8, 3, True), (9, 2, True),
                            (13, 4, True), (16, 0, False), (24, 0, False), (24, 0, True)]:
        net, data, cert = build(n, leaf, square)
        bits = n if square else 2 * n
        assert M.simulate(net, n, square, exhaustive=bits <= 16), (n, leaf, square)
        res = C.verify(data, cert)
        assert res["ok"], (n, leaf, square, res)
    net, data, cert = build(8, 3, False)
    lines = data.decode().split("\n")
    rows = [i for i, l in enumerate(lines) if l.endswith(" 1") and not l.startswith(".")]
    rejected = 0
    for i in rows[::7]:                                   # drop one minterm
        bad = "\n".join(lines[:i] + lines[i + 1:]).encode()
        got = C.verify(bad, dict(cert, netlist_digest="sha256:" + hashlib.sha256(bad).hexdigest()))["ok"]
        assert not got or truth(bad, 8), i               # nothing false is ever accepted
        rejected += not got
    assert rejected > 150
    assert not C.verify(data, dict(cert, n=7))["ok"]
    wrong = dict(cert, blocks=[dict(b, expr=[[2, e[1]] for e in b["expr"]]) if j == 0 else b for j, b in enumerate(cert["blocks"])])
    assert not C.verify(data, wrong)["ok"]
    print("ok")


if __name__ == "__main__":
    main()
