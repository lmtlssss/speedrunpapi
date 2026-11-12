"""Tests: random linear maps, CRC networks for several polynomials and bus sizes, and tamper rejection."""
import hashlib
import json
import random

import crc_gen
import independent_crc_checker as CC
import independent_linear_checker as LC
import linear_compiler as L


def forms(nodes, outs, nin):
    val = {i: 1 << i for i in range(nin)}
    for j, fan in enumerate(nodes):
        v = 0
        for x in fan:
            v ^= val[x]
        val[nin + j] = v
    return [0 if o is None else val[o] for o in outs]


def main():
    rnd = random.Random(11)
    for trial in range(60):
        nin, nout, k = rnd.randrange(2, 40), rnd.randrange(1, 24), rnd.choice((3, 4, 6))
        rows = [rnd.getrandbits(nin) for _ in range(nout)]
        nodes, outs, lev = L.build(rows, nin, k)
        assert forms(nodes, outs, nin) == rows and all(len(f) <= k for f in nodes)
    print("60 random linear maps: outputs equal the rows")
    for poly, width, data in ((0x04C11DB7, 32, 64), (0x1021, 16, 32), (0x1EDC6F41, 32, 128)):
        rows = L.crc_rows(poly, width, data)
        nodes, outs, lev = L.compile_linear(rows, width + data, 6, None)
        raw = L.blif(nodes, outs, ["s[%d]" % i for i in range(width)] + ["d[%d]" % i for i in range(data)], ["o[%d]" % i for i in range(width)], "crc")
        cert = {"schema": "colony.lut-linear.v1", "kind": "crc", "poly": poly, "width": width, "data": data, "k": 6,
                "lut_count": len(nodes), "levels": lev, "netlist_digest": "sha256:" + hashlib.sha256(raw).hexdigest()}
        assert LC.verify(raw, cert)["ok"]
    print("3 fixed-width CRC networks accepted")
    total = rejected = 0
    for poly, width, nbytes, k in ((0x04C11DB7, 32, 8, 6), (0x1021, 16, 5, 6), (0x04C11DB7, 32, 3, 4), (0x1EDC6F41, 32, 16, 6)):
        luts, lev, ebits = crc_gen.generate(poly, width, nbytes, k)
        raw = crc_gen.blif(luts, width, nbytes, ebits)
        cert = {"schema": "colony.lut-crc.v1", "poly": poly, "width": width, "bytes": nbytes, "k": k,
                "lut_count": sum(1 for nm, _, _ in luts if not nm.startswith("o[")), "levels": lev,
                "netlist_digest": "sha256:" + hashlib.sha256(raw).hexdigest()}
        res = CC.verify(raw, cert)
        assert res["ok"], res
        lines = raw.decode().split("\n")
        idx = [i for i, l in enumerate(lines) if l and l[0] in "01" and l.endswith(" 1") and len(l) > 3]
        for _ in range(40):
            i = rnd.choice(idx)
            data = "\n".join(lines[:i] + lines[i + 1:]).encode()
            total += 1
            rejected += not CC.verify(data, dict(cert, netlist_digest="sha256:" + hashlib.sha256(data).hexdigest()))["ok"]
    print("4 variable-length CRC networks accepted; %d of %d altered netlists rejected" % (rejected, total))
    assert rejected == total


if __name__ == "__main__":
    main()
