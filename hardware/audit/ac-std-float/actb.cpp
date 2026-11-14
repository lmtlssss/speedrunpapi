// Every operand of a small ac_std_float<W,E> format through one operation of the library, results as hex lines.
// usage: actb OP FORMAT ROUNDING [NOSUB]
//   OP        add sub mult div sqrt fma, ceil floor trunc round, lt le gt ge eq ne
//   FORMAT    one of the formats instantiated in main, written W.E: total width and exponent width
//             (5.2 6.2 6.3 7.2 7.3 8.3 8.4 9.3 9.4 10.3 10.4 11.3 11.4)
//   ROUNDING  conv (nearest, ties to even)  zero (truncate)  inf (nearest, ties away)  odd (nearest, ties to odd)
//             the library's AC_RND_CONV, AC_TRN_ZERO, AC_RND_INF and AC_RND_CONV_ODD
//   NOSUB     any fourth argument selects the library's No_SubNormals variant
// Order of the lines: a ascending; for two operands a outer and b inner; for fma a, b, c with c innermost.
#include <ac_std_float.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>

template<int W, int E, ac_q_mode QR, bool NS>
static void run(const char *op) {
  typedef ac_std_float<W, E> F;
  const unsigned long n = 1UL << W;
  const unsigned long mask = n - 1;
  F x, y, z, r;
  if (!strcmp(op, "ceil") || !strcmp(op, "floor") || !strcmp(op, "trunc") || !strcmp(op, "round")) {
    for (unsigned long a = 0; a < n; a++) {
      x.d = a;
      if (!strcmp(op, "ceil")) r = x.ceil();
      else if (!strcmp(op, "floor")) r = x.floor();
      else if (!strcmp(op, "trunc")) r = x.trunc();
      else r = x.round();
      printf("%lx\n", (unsigned long) r.d.to_uint64() & mask);
    }
    return;
  }
  if (!strcmp(op, "lt") || !strcmp(op, "le") || !strcmp(op, "gt") || !strcmp(op, "ge") || !strcmp(op, "eq") || !strcmp(op, "ne")) {
    for (unsigned long a = 0; a < n; a++) {
      x.d = a;
      for (unsigned long b = 0; b < n; b++) {
        y.d = b;
        bool t;
        if (!strcmp(op, "lt")) t = x < y;
        else if (!strcmp(op, "le")) t = x <= y;
        else if (!strcmp(op, "gt")) t = x > y;
        else if (!strcmp(op, "ge")) t = x >= y;
        else if (!strcmp(op, "eq")) t = x == y;
        else t = x != y;
        printf("%d\n", t ? 1 : 0);
      }
    }
    return;
  }
  if (!strcmp(op, "sqrt")) {
    for (unsigned long a = 0; a < n; a++) {
      x.d = a;
      r = x.template sqrt<QR, NS>();
      printf("%lx\n", (unsigned long) r.d.to_uint64() & mask);
    }
    return;
  }
  if (!strcmp(op, "fma")) {
    for (unsigned long a = 0; a < n; a++) {
      x.d = a;
      for (unsigned long b = 0; b < n; b++) {
        y.d = b;
        for (unsigned long c = 0; c < n; c++) {
          z.d = c;
          r = x.template fma<QR, NS>(y, z);
          printf("%lx\n", (unsigned long) r.d.to_uint64() & mask);
        }
      }
    }
    return;
  }
  for (unsigned long a = 0; a < n; a++) {
    x.d = a;
    for (unsigned long b = 0; b < n; b++) {
      y.d = b;
      if (!strcmp(op, "add")) r = x.template add<QR, NS>(y);
      else if (!strcmp(op, "sub")) r = x.template sub<QR, NS>(y);
      else if (!strcmp(op, "mult")) r = x.template mult<QR, NS>(y);
      else r = x.template div<QR, NS>(y);
      printf("%lx\n", (unsigned long) r.d.to_uint64() & mask);
    }
  }
}

template<int W, int E>
static void pick(const char *op, const char *rnd, bool ns) {
  if (!strcmp(rnd, "conv")) { if (ns) run<W, E, AC_RND_CONV, true>(op); else run<W, E, AC_RND_CONV, false>(op); }
  else if (!strcmp(rnd, "zero")) { if (ns) run<W, E, AC_TRN_ZERO, true>(op); else run<W, E, AC_TRN_ZERO, false>(op); }
  else if (!strcmp(rnd, "inf")) { if (ns) run<W, E, AC_RND_INF, true>(op); else run<W, E, AC_RND_INF, false>(op); }
  else { if (ns) run<W, E, AC_RND_CONV_ODD, true>(op); else run<W, E, AC_RND_CONV_ODD, false>(op); }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: actb OP W.E ROUNDING [NOSUB]\n"); return 2; }
  const char *op = argv[1], *fmt = argv[2], *rnd = argv[3];
  bool ns = argc > 4;
  if (!strcmp(fmt, "8.3")) pick<8, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "8.4")) pick<8, 4>(op, rnd, ns);
  else if (!strcmp(fmt, "10.4")) pick<10, 4>(op, rnd, ns);
  else if (!strcmp(fmt, "6.3")) pick<6, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "7.3")) pick<7, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "5.2")) pick<5, 2>(op, rnd, ns);
  else if (!strcmp(fmt, "6.2")) pick<6, 2>(op, rnd, ns);
  else if (!strcmp(fmt, "7.2")) pick<7, 2>(op, rnd, ns);
  else if (!strcmp(fmt, "9.3")) pick<9, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "9.4")) pick<9, 4>(op, rnd, ns);
  else if (!strcmp(fmt, "10.3")) pick<10, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "11.3")) pick<11, 3>(op, rnd, ns);
  else if (!strcmp(fmt, "11.4")) pick<11, 4>(op, rnd, ns);
  else { fprintf(stderr, "format not built in\n"); return 2; }
  return 0;
}
