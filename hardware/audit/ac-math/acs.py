# Exhaustive check of ac_math::ac_shift_left and ac_math::ac_shift_right on small ac_fixed types.
#
# usage: python3 acs.py gen OUT_DIR [PARTS]
#        python3 acs.py check OUT_DIR RESULTS.txt [examples]
#        python3 acs.py depends OUT_DIR RESULTS_A.txt RESULTS_B.txt [examples]
#
# A configuration is one instantiation: the operand type, the output type with its quantization and overflow mode,
# signed or unsigned, the direction, and whether the shift count is an int or an unsigned int. Every operand value
# is shifted by every count from -10 (0 for an unsigned count) to 10. The reference is the operand times a power of
# two, as a fraction, quantized once into the output type. It reuses the definitions of acm.py.
import sys
from fractions import Fraction

import acm

X = [(4, 2), (4, 4), (3, 0), (4, 6), (3, -1)]
O = [(5, 3), (6, 2), (4, 4), (4, 0), (3, -1), (8, 4)]
NMAX = 10


def configs():
    out = []
    for left in (0, 1):
        for s in (0, 1):
            for ns in (0, 1):
                for x in X:
                    for o in O:
                        for qq in acm.QMODES:
                            for qo in acm.OMODES:
                                out.append({"op": "shift", "left": left, "s": s, "ns": ns, "x": x, "o": o, "qq": qq, "qo": qo})
    for i, c in enumerate(out):
        c["id"] = i
    return out


HEAD = acm.HEAD.replace("int main(int argc, char **argv) {", r'''#include <ac_math/ac_shift.h>
template<int XW, int XI, int OW, int OI, ac_q_mode OQ, ac_o_mode OO, bool S, bool LEFT, bool NS>
static void shift_(int id) {
  for (unsigned x = 0; x < (1u << XW); x++)
    for (int n = (NS ? -%d : 0); n <= %d; n++) {
      try {
        ac_fixed<OW, OI, S, OQ, OO> r;
        r.set_slc(0, ac_int<OW, false>(SENT));
        if (LEFT) {
          if (NS) ac_math::ac_shift_left(raw<XW, XI, S>(x), n, r);
          else ac_math::ac_shift_left(raw<XW, XI, S>(x), (unsigned) n, r);
        } else {
          if (NS) ac_math::ac_shift_right(raw<XW, XI, S>(x), n, r);
          else ac_math::ac_shift_right(raw<XW, XI, S>(x), (unsigned) n, r);
        }
        printf("%%d %%x %%d %%llx\n", id, x, n, bits(r));
      } catch (const ac_fail &f) { printf("%%d %%x %%d A %%d\n", id, x, n, f.line); }
    }
}

int main(int argc, char **argv) {''' % (NMAX, NMAX))


def call(c):
    b = lambda v: "true" if v else "false"
    return "  shift_<%d, %d, %d, %d, %s, %s, %s, %s, %s>(%d);\n" % (*c["x"], *c["o"], c["qq"], c["qo"], b(c["s"]), b(c["left"]), b(c["ns"]), c["id"])


def expected(c, f):
    s = c["s"]
    x = acm.value(int(f[1], 16), *c["x"], s)
    n = int(f[2])
    v = x * Fraction(2) ** (n if c["left"] else -n)
    ow, oi = c["o"]
    return acm.overflow(acm.quantize(v * Fraction(2) ** (ow - oi), c["qq"]), ow, s, c["qo"]), int(f[3], 16), None


def describe(c):
    return "ac_shift_%s %s ac_fixed<%d,%d> by %s -> <%d,%d,%s,%s>" % (
        "left" if c["left"] else "right", "signed" if c["s"] else "unsigned", *c["x"], "an int" if c["ns"] else "an unsigned", *c["o"], c["qq"], c["qo"])


acm.configs, acm.HEAD, acm.call, acm.expected, acm.describe = configs, HEAD, call, expected, describe

if __name__ == "__main__":
    if sys.argv[1] == "gen":
        acm.gen(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 8)
    elif sys.argv[1] == "depends":
        acm.depends(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]) if len(sys.argv) > 5 else 6)
    else:
        acm.check(sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 2)
