"""Square root and hypotenuse: recurrence model, exhaustive simulation, proof replay, tamper rejection."""
import hashlib
import math
import sqrt_compiler as S
import hyp_compiler as H
import independent_sqrt_checker as C


def model(a, m):
    """The recurrence in the checker's header, with its word widths."""
    r, q = 0, 0
    for k in range(1, m + 1):
        w = k + 2
        pair = (a >> (2 * (m - k))) & 3
        s = 1 if r < 0 else 0
        t = sum((1 ^ ((q >> j) & 1) ^ s) << j for j in range(k))
        v = (4 * (r % (1 << w)) + pair + 3 + 4 * t) % (1 << w)
        r = v - (1 << w) if v >> (w - 1) else v
        q = 2 * q + (r >= 0)
    return q


def main():
    for m in range(1, 10):                               # the recurrence itself, every operand
        assert all(model(a, m) == math.isqrt(a) for a in range(1 << (2 * m))), m
    for m in (1, 2, 3, 5, 8):
        net = S.compile_sqrt(m)
        data = S.blif(net, m)
        assert S.simulate(net, m, exhaustive=True)
        assert C.verify(data, S.certificate(net, m, data))["ok"], m
    for n in (2, 3, 5, 8):
        net = H.compile_hyp(n)
        data = H.blif(net, n)
        assert H.simulate(net, n, exhaustive=True)
        assert C.verify(data, S.certificate(net, n, data, "hyp", net.blocks))["ok"], n
    for build, sim in ((lambda: (S.compile_sqrt(8), 8, "sqrt"), S.simulate), (lambda: (H.compile_hyp(6), 6, "hyp"), H.simulate)):
        net, size, kind = build()
        data = (S.blif if kind == "sqrt" else H.blif)(net, size)
        cert = S.certificate(net, size, data, kind, getattr(net, "blocks", None) if kind == "hyp" else None)
        lines = data.decode().split("\n")
        rows = [i for i, l in enumerate(lines) if l.endswith(" 1") and not l.startswith(".")]
        rejected = accepted = 0
        for i in rows[::5]:                              # drop one minterm
            bad_lines = lines[:i] + lines[i + 1:]
            bad = "\n".join(bad_lines).encode()
            ok = C.verify(bad, dict(cert, netlist_digest="sha256:" + hashlib.sha256(bad).hexdigest()))["ok"]
            if ok:                                       # accepted: the function must be unchanged
                net2 = type(net)()
                net2.luts, cur = [], None
                for l in bad_lines:
                    t = l.split()
                    if t and t[0] == ".names":
                        cur = [t[-1], t[1:-1], 0]
                        net2.luts.append(cur)
                    elif cur and len(t) == 2 and t[1] == "1":
                        cur[2] |= 1 << sum(1 << j for j, ch in enumerate(t[0]) if ch == "1")
                    elif cur and t == ["1"]:
                        cur[2] = 1
                net2.luts = [tuple(x) for x in net2.luts]
                assert sim(net2, size, exhaustive=True), (kind, i)
                accepted += 1
            else:
                rejected += 1
        assert rejected > 20, (kind, rejected, accepted)
    print("ok")


if __name__ == "__main__":
    main()
