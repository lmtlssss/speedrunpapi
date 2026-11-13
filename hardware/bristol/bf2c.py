"""Turns FP-add.txt, FP-mul.txt, FP-div.txt and FP-sqrt.txt of this folder into C functions for native.c.

usage: python3 bf2c.py [OUTDIR]        writes c_add.h, c_mul.h, c_div.h, c_sqrt.h (into OUTDIR, default: here)

Each function works on 64-bit words: a word carries one wire for 64 operand vectors at once.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def convert(src, name, dst):
    with open(src) as f:
        lines = [t.split() for t in f.read().split("\n") if t.strip()]
    nwires = int(lines[0][1])
    nin = sum(int(x) for x in lines[1][1:1 + int(lines[1][0])])
    nout = sum(int(x) for x in lines[2][1:1 + int(lines[2][0])])
    out = ["static void %s(const uint64_t *in, uint64_t *out) {" % name,
           "  static uint64_t w[%d];" % nwires,
           "  for (int i = 0; i < %d; i++) w[i] = in[i];" % nin]
    for t in lines[3:]:
        if t[-1] == "XOR":
            out.append("  w[%s] = w[%s] ^ w[%s];" % (t[4], t[2], t[3]))
        elif t[-1] == "AND":
            out.append("  w[%s] = w[%s] & w[%s];" % (t[4], t[2], t[3]))
        elif t[-1] == "INV":
            out.append("  w[%s] = ~w[%s];" % (t[3], t[2]))
        else:
            raise ValueError("gate " + t[-1])
    out.append("  for (int i = 0; i < %d; i++) out[i] = w[%d + i];" % (nout, nwires - nout))
    out.append("}")
    with open(dst, "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    outdir = sys.argv[1] if len(sys.argv) > 1 else HERE
    os.makedirs(outdir, exist_ok=True)
    for op in ("add", "mul", "div", "sqrt"):
        convert(os.path.join(HERE, "FP-%s.txt" % op), "c_" + op, os.path.join(outdir, "c_%s.h" % op))
