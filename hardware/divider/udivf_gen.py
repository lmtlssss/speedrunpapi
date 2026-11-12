"""Fold divider as RTL.  usage: udivf_gen.py WIDTH [FOLD] > udivfWIDTH.v"""
import sys


def gen(n, b=8):
    g = b + 2
    t = m = g + 2
    k = -(-n // b)
    P = n - 1 + m
    npad = k * b
    assert n >= t, "width below %d needs a smaller fold" % t
    # entry for the top t bits idx of dn: the largest m with m * dn <= 2**P for every dn under idx
    tab = {idx: (1 << P) // (((idx + 1) << (n - t)) - 1) for idx in range(1 << (t - 1), 1 << t)}
    we = P - g
    lg = max(1, (n - 1).bit_length())
    L = ["// Unsigned divider, combinational.  q = a / b, r = a % b.  b = 0 gives q = all ones, r = a.",
         "// Fold division: dn = b << lzc(b).  A table read from the top %d bits of dn gives m with" % t,
         "// m * dn in (2**%d - 2**%d, 2**%d];  eps = 2**%d - m * dn." % (P, P - g, P, P),
         "// Since t * 2**%d = t * (m * dn) + t * eps, the top field t of the running value folds back as t * eps:" % P,
         "// %d quotient bits per fold.  qa = sum of the fields; a - qa * b lies in [0, 3b)." % b,
         "module udivf%d (input [%d:0] a, input [%d:0] b, output [%d:0] q, output [%d:0] r);" % (n, n - 1, n - 1, n - 1, n - 1),
         "  function [%d:0] rom(input [%d:0] i);" % (m - 1, t - 2), "    case (i)"]
    for idx in range(1 << (t - 1), 1 << t):
        L.append("      %d'd%d: rom = %d'd%d;" % (t - 1, idx - (1 << (t - 1)), m, tab[idx]))
    L += ["    endcase", "  endfunction",
          "  reg [%d:0] s; integer i;" % (lg - 1),
          "  always @* begin s = 0; for (i = 0; i < %d; i = i + 1) if (b[i]) s = %d - i; end" % (n, n - 1),
          "  wire [%d:0] dn = b << s;" % (n - 1),
          "  wire [%d:0] x = {%d'd0, a} << s;" % (2 * n - 2, n - 1),
          "  wire [%d:0] m = rom(dn[%d:%d]);" % (m - 1, n - 2, n - t),
          "  wire [%d:0] eps = {1'b1, %d'd0} - m * dn;" % (we - 1, P),
          "  wire [%d:0] w0 = m * x;" % (P + n - 1)]
    prev, pw, terms, tw = "w0", P + n, [], 0
    for i in range(k):
        p = P + npad - (i + 1) * b
        off = p - P
        tw = pw - p
        if tw <= 0:
            continue
        L.append("  wire [%d:0] t%d = %s[%d:%d];" % (tw - 1, i, prev, pw - 1, p))
        terms.append("({%d'd0, t%d} << %d)" % (n, i, off) if off else "{%d'd0, t%d}" % (n, i))
        if i == k - 1:
            break
        L.append("  wire [%d:0] w%d = %s[%d:0] + ((t%d * eps) << %d);" % (p + 1, i + 1, prev, p - 1, i, off))
        prev, pw = "w%d" % (i + 1), p + 2
    L += ["  wire [%d:0] qa = %s;" % (n + tw, " + ".join(terms)),
          "  wire [%d:0] r0 = {2'b0, a} - qa[%d:0] * b;" % (n + 1, n - 1),
          "  wire [%d:0] r1 = r0 - {2'b0, b};" % (n + 1),
          "  wire [%d:0] r2 = r0 - {1'b0, b, 1'b0};" % (n + 1),
          "  wire z = ~|b;",
          "  assign q = z ? {%d{1'b1}} : !r2[%d] ? qa[%d:0] + 2 : !r1[%d] ? qa[%d:0] + 1 : qa[%d:0];" % (n, n + 1, n - 1, n + 1, n - 1, n - 1),
          "  assign r = z ? a : !r2[%d] ? r2[%d:0] : !r1[%d] ? r1[%d:0] : r0[%d:0];" % (n + 1, n - 1, n + 1, n - 1, n - 1),
          "endmodule"]
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    sys.stdout.write(gen(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 8))
