"""CRC generator for wide buses with a variable number of valid bytes.

Ports: s (register in), d (bus, bit d[0] first on the wire), e (number of empty bytes at the end of the bus,
binary), o (register out).  Bytes past the valid ones must be zero.

Structure: one network computes the register after the whole bus, F(s, d).  Zero bytes at the end advance the
register by a fixed linear map A^8 each, so the register after the valid bytes is A^(-8e) F(s, d).  A^(-8e) is
applied as one conditional stage per bit of e:  x' = x ^ (e_j & (U_j + I) x),  U_j = A^(-8 * 2^j).
Every XOR network is built by linear_compiler.
"""
import argparse
import hashlib
import json
from pathlib import Path

import linear_compiler as L


def advance(poly, width, nbits):
    rows = [1 << i for i in range(width)]
    for _ in range(nbits):
        fb = rows[width - 1]
        rows = [(rows[i - 1] if i else 0) ^ (fb if (poly >> i) & 1 else 0) for i in range(width)]
    return rows


def invert(rows, n):
    a = [rows[i] | (1 << (n + i)) for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if (a[r] >> c) & 1)
        a[c], a[p] = a[p], a[c]
        for r in range(n):
            if r != c and (a[r] >> c) & 1:
                a[r] ^= a[c]
    return [a[i] >> n for i in range(n)]


def generate(poly, width, nbytes, k=6, depth=None):
    """Returns (luts, levels): luts = [(name, [inputs], truth table int)] in topological order."""
    nbits = 8 * nbytes
    ebits = max(1, (nbytes - 1).bit_length()) if nbytes > 1 else 0
    ins = ["s[%d]" % i for i in range(width)] + ["d[%d]" % i for i in range(nbits)]
    parity = lambda n: sum(1 << r for r in range(1 << n) if L.pc(r) & 1)
    luts, level = [], {v: 0 for v in ins}
    for j in range(ebits):
        level["e[%d]" % j] = 0

    def add(name, src, tt):
        luts.append((name, list(src), tt))
        level[name] = 1 + max(level[v] for v in src)
        return name
    nodes, outs, _ = L.compile_linear(L.crc_rows(poly, width, nbits), width + nbits, k, depth)
    names = list(ins)
    for q, fan in enumerate(nodes):
        names.append(add("f%d" % q, [names[v] for v in fan], parity(len(fan))))
    x = [names[o] for o in outs]
    cuts = []
    for j in range(ebits):
        cuts.append((len(luts), list(x)))
        U = invert(advance(poly, width, 8 << j), width)
        rows = [U[i] ^ (1 << i) for i in range(width)]
        sk = k - 2 if k >= 5 else k
        nodes, outs, _ = L.compile_linear(rows, width, sk)
        names = list(x)
        for q, fan in enumerate(nodes):
            names.append(("u%d_%d" % (j, q), fan))
        made = {}

        def wire(v):
            if v < width:
                return x[v]
            nm, fan = names[v]
            if nm not in made:
                made[nm] = add(nm, [wire(u) for u in fan], parity(len(fan)))
            return made[nm]
        nx = []
        for i in range(width):
            o = outs[i]
            if o is None:
                nx.append(x[i])
                continue
            if k >= 5 and o >= width:                        # the last parity, the gate and the bypass in one LUT
                fan = [wire(u) for u in names[o][1]]
            else:
                fan = [wire(o)]
            src = fan + ["e[%d]" % j] + ([x[i]] if x[i] not in fan else [])
            nf = len(fan)
            own = src.index(x[i])
            tt = 0
            for r in range(1 << len(src)):
                t = L.pc(r & ((1 << nf) - 1)) & 1
                if ((r >> own) & 1) ^ (t & ((r >> nf) & 1)):
                    tt |= 1 << r
            nx.append(add("x%d_%d" % (j, i), src, tt))
        x = nx
    cuts.append((len(luts), list(x)))
    generate.cuts = cuts                                     # (index into luts, register vector there)
    for i in range(width):
        add("o[%d]" % i, [x[i]], 0b10)
    return luts, max(level["o[%d]" % i] for i in range(width)) - 1, ebits


def blif(luts, width, nbytes, ebits):
    ins = ["s[%d]" % i for i in range(width)] + ["d[%d]" % i for i in range(8 * nbytes)] + ["e[%d]" % j for j in range(ebits)]
    out = [".model crc", ".inputs " + " ".join(ins), ".outputs " + " ".join("o[%d]" % i for i in range(width))]
    for name, src, tt in luts:
        out.append(".names " + " ".join(src + [name]))
        for r in range(1 << len(src)):
            if (tt >> r) & 1:
                out.append("".join("1" if (r >> q) & 1 else "0" for q in range(len(src))) + " 1")
    return ("\n".join(out) + "\n.end\n").encode()


def verilog(luts, width, nbytes, ebits, module, family=None):
    """family None: plain expressions.  'xilinx' or 'ecp5': LUT instances."""
    sane = lambda v: v
    V = ["// CRC register after the first (%d - e) bytes of d; bytes past them must be zero." % nbytes,
         "module %s (input [%d:0] s, input [%d:0] d, %soutput [%d:0] o);" % (
             module, width - 1, 8 * nbytes - 1, "input [%d:0] e, " % (ebits - 1) if ebits else "", width - 1)]
    for name, src, tt in luts:
        n = len(src)
        if name.startswith("o["):
            V.append("  assign %s = %s;" % (name, src[0]))
        elif family == "xilinx":
            V.append("  wire %s; LUT%d #(.INIT(%d'h%x)) i_%s (.O(%s), %s);" % (name, n, 1 << n, tt, name, name, ", ".join(".I%d(%s)" % (q, v) for q, v in enumerate(src))))
        elif family == "ecp5":
            assert n <= 4
            init = sum(((tt >> (r & ((1 << n) - 1))) & 1) << r for r in range(16))
            pins = src + ["1'b0"] * (4 - n)
            V.append("  wire %s; LUT4 #(.INIT(16'h%04x)) i_%s (.Z(%s), .A(%s), .B(%s), .C(%s), .D(%s));" % ((name, init, name, name) + tuple(pins)))
        else:
            V.append("  wire %s = %d'h%x >> {%s};" % (name, 1 << n, tt, ", ".join(reversed(src))))
    V.append("endmodule")
    return "\n".join(V) + "\n"


def verilog_pipelined(luts, cuts, width, nbytes, ebits, module, family=None):
    """One register stage after the full-bus network and after each conditional stage.
    Latency: len(cuts) clocks.  e is delayed alongside."""
    V = ["// CRC register after the first (%d - e) bytes of d; bytes past them must be zero.  Latency %d clocks." % (nbytes, len(cuts)),
         "module %s (input clk, input [%d:0] s, input [%d:0] d, %soutput [%d:0] o);" % (
             module, width - 1, 8 * nbytes - 1, "input [%d:0] e, " % (ebits - 1) if ebits else "", width - 1)]
    ren, ecur = {}, "e"
    at = {pos: vec for pos, vec in cuts}
    stage = 0
    for q, (name, src, tt) in enumerate(luts):
        if q in at:
            stage += 1
            vec = at[q]
            V.append("  reg [%d:0] r%d;" % (width - 1, stage))
            V.append("  always @(posedge clk) r%d <= {%s};" % (stage, ", ".join(ren.get(v, v) for v in reversed(vec))))
            for i, v in enumerate(vec):
                ren[v] = "r%d[%d]" % (stage, i)
            if ebits:
                V.append("  reg [%d:0] e%d; always @(posedge clk) e%d <= %s;" % (ebits - 1, stage, stage, ecur))
                ecur = "e%d" % stage
        n = len(src)
        ins = [(ecur + v[1:]) if v.startswith("e[") else ren.get(v, v) for v in src]
        if name.startswith("o["):
            V.append("  assign %s = %s;" % (name, ins[0]))
        elif family == "xilinx":
            V.append("  wire %s; LUT%d #(.INIT(%d'h%x)) i_%s (.O(%s), %s);" % (name, n, 1 << n, tt, name, name, ", ".join(".I%d(%s)" % (t, v) for t, v in enumerate(ins))))
        elif family == "ecp5":
            assert n <= 4
            init = sum(((tt >> (r & ((1 << n) - 1))) & 1) << r for r in range(16))
            pins = ins + ["1'b0"] * (4 - n)
            V.append("  wire %s; LUT4 #(.INIT(16'h%04x)) i_%s (.Z(%s), .A(%s), .B(%s), .C(%s), .D(%s));" % ((name, init, name, name) + tuple(pins)))
        else:
            V.append("  wire %s = %d'h%x >> {%s};" % (name, 1 << n, tt, ", ".join(reversed(ins))))
    V.append("endmodule")
    return "\n".join(V) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--poly", default="0x04C11DB7")
    ap.add_argument("--width", type=int, default=32)
    ap.add_argument("--bytes", type=int, required=True)
    ap.add_argument("--k", type=int, default=6)
    ap.add_argument("--depth", type=int)
    ap.add_argument("--family", choices=["xilinx", "ecp5"])
    ap.add_argument("--pipeline", action="store_true", help="also write crc_pipe.v with a register after each stage")
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    poly = int(a.poly, 0)
    luts, lev, ebits = generate(poly, a.width, a.bytes, a.k, a.depth)
    data = blif(luts, a.width, a.bytes, ebits)
    count = sum(1 for name, _, _ in luts if not name.startswith("o["))
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / "crc.blif").write_bytes(data)
        (a.out / "crc.v").write_text(verilog(luts, a.width, a.bytes, ebits, "crc%d_b%d" % (a.width, a.bytes), a.family))
        if a.pipeline:
            (a.out / "crc_pipe.v").write_text(verilog_pipelined(luts, generate.cuts, a.width, a.bytes, ebits, "crc%d_b%d_pipe" % (a.width, a.bytes), a.family))
        (a.out / "crc.json").write_text(json.dumps({"schema": "colony.lut-crc.v1", "poly": poly, "width": a.width, "bytes": a.bytes, "k": a.k,
                                                    "lut_count": count, "levels": lev, "netlist_digest": "sha256:" + hashlib.sha256(data).hexdigest()}, sort_keys=True) + "\n")
    print(json.dumps({"bytes": a.bytes, "k": a.k, "lut_count": count, "levels": lev}))
