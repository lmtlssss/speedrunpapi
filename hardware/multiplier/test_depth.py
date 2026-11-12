"""Depth builds: exhaustive simulation, proof replay, tamper rejection."""
import hashlib
import mul_compiler as M
import mul_depth as D
import independent_depth_checker as C


def truth(data, n, square):
    ins, outs, tables = C.parse_blif(data)
    bits = n if square else 2 * n
    S = 1 << bits
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
        a = s & ((1 << n) - 1)
        b = a if square else s >> n
        if sum(((env[o] >> s) & 1) << i for i, o in enumerate(outs)) != a * b:
            return False
    return True


def main():
    for n, square in [(2, False), (3, False), (5, False), (8, False), (3, True), (8, True), (13, True), (16, True)]:
        net = (D.compile_square_depth if square else D.compile_mul_depth)(n)
        data = M.blif(net, n, square)
        assert M.simulate(net, n, square, exhaustive=(n if square else 2 * n) <= 16), (n, square)
        assert C.verify(data, D.certificate(net, data))["ok"], (n, square)
    for n, square in [(4, False), (7, True)]:
        net = (D.compile_square_depth if square else D.compile_mul_depth)(n)
        data = M.blif(net, n, square)
        cert = D.certificate(net, data)
        lines = data.decode().split("\n")
        rows = [i for i, l in enumerate(lines) if l.endswith(" 1") and not l.startswith(".")]
        rejected = 0
        for i in rows[::9]:                                # drop one minterm
            bad = "\n".join(lines[:i] + lines[i + 1:]).encode()
            ok = C.verify(bad, dict(cert, netlist_digest="sha256:" + hashlib.sha256(bad).hexdigest()))["ok"]
            assert not ok or truth(bad, n, square), (n, square, i)   # nothing false is ever accepted
            rejected += not ok
        assert rejected > 20, (n, square, rejected)
    print("ok")


if __name__ == "__main__":
    main()
