"""Divider: recurrence model, exhaustive simulation, proof replay, tamper rejection."""
import hashlib
import div_compiler as D
import independent_div_checker as C


def model(a, b, n):
    """The recurrence in the checker's header, with its word widths."""
    r, s, q = 0, 0, 0
    for j in range(1, n + 1):
        w = j + 1
        bit = (a >> (n - j)) & 1
        t = sum((1 ^ ((b >> c) & 1 if c < n else 0) ^ s) << c for c in range(w))
        r = (2 * r + bit + t + (1 - s)) % (1 << w)
        s = 1 if (b >> j) or (r >> j) else 0
        q = 2 * q + (1 - s)
    return q, (r + (b if s else 0)) % (1 << n)


def main():
    for n in range(1, 9):                                # the recurrence itself, every operand pair
        for a in range(1 << n):
            for b in range(1 << n):
                assert model(a, b, n) == ((a // b, a % b) if b else ((1 << n) - 1, a)), (n, a, b)
    for n in (1, 2, 3, 5, 8):
        net = D.compile_div(n)
        data = D.blif(net, n)
        assert D.simulate(net, n, exhaustive=True)
        assert C.verify(data, D.certificate(net, n, data))["ok"], n
    net = D.compile_div(7)
    data = D.blif(net, 7)
    cert = D.certificate(net, 7, data)
    lines = data.decode().split("\n")
    rows = [i for i, l in enumerate(lines) if l.endswith(" 1") and not l.startswith(".")]
    rejected = 0
    for i in rows[::5]:                                  # drop one minterm
        bad_lines = lines[:i] + lines[i + 1:]
        bad = "\n".join(bad_lines).encode()
        if C.verify(bad, dict(cert, netlist_digest="sha256:" + hashlib.sha256(bad).hexdigest()))["ok"]:
            net2 = D.Net()                               # accepted: the function must be unchanged
            net2.luts, cur = [], None
            for l in bad_lines:
                t = l.split()
                if t and t[0] == ".names":
                    cur = [t[-1], t[1:-1], 0]
                    net2.luts.append(cur)
                elif cur and len(t) == 2 and t[1] == "1":
                    cur[2] |= 1 << sum(1 << k for k, ch in enumerate(t[0]) if ch == "1")
            net2.luts = [tuple(x) for x in net2.luts]
            assert D.simulate(net2, 7, exhaustive=True), i
        else:
            rejected += 1
    assert rejected > 40, rejected
    print("ok")


if __name__ == "__main__":
    main()
