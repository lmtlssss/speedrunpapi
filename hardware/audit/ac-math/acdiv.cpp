// ac_math::ac_div on fixed-point types whose quotient is smaller than the last place of the output type.
#include <ac_fixed.h>
#include <ac_math/ac_div.h>
#include <cstdio>

int main() {
  {
    // unsigned: a fraction divided by an integer into an integer type. 0.5 / 3 = 0.1666..., so the quotient is 0.
    ac_fixed<8, 0, false> n = 0.5;
    ac_fixed<8, 8, false> d = 3;
    ac_fixed<8, 8, false> q = 77;                      // what the variable held before the call
    bool rem = ac_math::ac_div(n, d, q);
    printf("unsigned  0.5 / 3    -> %g   returned %d   (0 is right)\n", q.to_double(), (int) rem);
  }
  {
    // signed, truncation toward minus infinity (AC_TRN, the default): floor(-0.5 / 3) = -1.
    ac_fixed<8, 0, true> n = -0.5;
    ac_fixed<8, 8, true> d = 3;
    ac_fixed<8, 8, true> q = 77;
    bool rem = ac_math::ac_div(n, d, q);
    printf("signed   -0.5 / 3    -> %g   returned %d   (-1 is right: AC_TRN rounds toward minus infinity)\n", q.to_double(), (int) rem);
  }
  {
    // signed, ties away from zero, saturating output with a last place of 2: -2 / 2 = -1 is a tie between 0 and -2.
    ac_fixed<4, 2, true> n = -2;
    ac_fixed<3, 4, true> d = 2;
    ac_fixed<5, 6, true, AC_RND_INF, AC_SAT> q = 30;
    bool rem = ac_math::ac_div(n, d, q);
    printf("signed   -2 / 2      -> %g   returned %d   (-2 is right: AC_RND_INF rounds a tie away from zero)\n", q.to_double(), (int) rem);
  }
  return 0;
}
