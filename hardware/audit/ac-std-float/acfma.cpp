// One fused multiply-add in binary32 and one in binary64, in the library's four rounding modes.
// a * b + c lies exactly halfway between the largest number below 2 and 2 itself:
//   binary32  2^-12 * 2^-12 + (2 - 2^-23) = 2 - 2^-24
//   binary64  2^-27 * 2^-26 + (2 - 2^-52) = 2 - 2^-53
// To nearest with ties to even or ties away the answer is 2; truncated, or with ties to odd, it is the number
// just below 2 (its last bit is 1). The last line of each block does the same sum as a multiply and then an add.
#include <ac_std_float.h>
#include <cstdio>

int main() {
  {
    typedef ac_std_float<32, 8> F;
    F a, b, c;
    a.d = 0x39800000;   // 2^-12
    b.d = 0x39800000;   // 2^-12
    c.d = 0x3FFFFFFF;   // 2 - 2^-23
    printf("binary32  fma(2^-12, 2^-12, 2 - 2^-23)\n");
    printf("  AC_RND_CONV      %08x\n", (unsigned) a.fma<AC_RND_CONV, false>(b, c).d.to_uint64());
    printf("  AC_TRN_ZERO      %08x\n", (unsigned) a.fma<AC_TRN_ZERO, false>(b, c).d.to_uint64());
    printf("  AC_RND_INF       %08x\n", (unsigned) a.fma<AC_RND_INF, false>(b, c).d.to_uint64());
    printf("  AC_RND_CONV_ODD  %08x\n", (unsigned) a.fma<AC_RND_CONV_ODD, false>(b, c).d.to_uint64());
    printf("  mult then add, AC_RND_CONV_ODD  %08x\n",
           (unsigned) a.mult<AC_RND_CONV_ODD, false>(b).add<AC_RND_CONV_ODD, false>(c).d.to_uint64());
  }
  {
    typedef ac_std_float<64, 11> F;
    F a, b, c;
    a.d = 0x3E40000000000000LL;   // 2^-27
    b.d = 0x3E50000000000000LL;   // 2^-26
    c.d = 0x3FFFFFFFFFFFFFFFLL;   // 2 - 2^-52
    printf("binary64  fma(2^-27, 2^-26, 2 - 2^-52)\n");
    printf("  AC_RND_CONV      %016llx\n", (unsigned long long) a.fma<AC_RND_CONV, false>(b, c).d.to_uint64());
    printf("  AC_TRN_ZERO      %016llx\n", (unsigned long long) a.fma<AC_TRN_ZERO, false>(b, c).d.to_uint64());
    printf("  AC_RND_INF       %016llx\n", (unsigned long long) a.fma<AC_RND_INF, false>(b, c).d.to_uint64());
    printf("  AC_RND_CONV_ODD  %016llx\n", (unsigned long long) a.fma<AC_RND_CONV_ODD, false>(b, c).d.to_uint64());
    printf("  mult then add, AC_RND_CONV_ODD  %016llx\n",
           (unsigned long long) a.mult<AC_RND_CONV_ODD, false>(b).add<AC_RND_CONV_ODD, false>(c).d.to_uint64());
  }
  return 0;
}
