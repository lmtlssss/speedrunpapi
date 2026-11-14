// Three conversions of ac_std_float in ordinary-looking formats.
#include <ac_std_float.h>
#include <cstdio>

int main() {
  {
    // 1. Same exponent width, shorter fraction: binary64's layout cut to 40 bits (28 fraction bits).
    //    The largest subnormal, (1 - 2^-52) x 2^-1022, rounds to the smallest normal number, 2^-1022.
    ac_std_float<64, 11> x;
    x.d = 0x000FFFFFFFFFFFFFLL;
    ac_std_float<40, 11> y(x);                                    // the constructor: convert<40, AC_RND_CONV>
    ac_std_float<40, 11> z = x.convert<40, AC_RND_INF>();
    printf("1. ac_std_float<64,11> 000fffffffffffff -> <40,11>   constructor %010llx   AC_RND_INF %010llx   (0010000000 is right)\n",
           (unsigned long long) y.d.to_uint64() & 0xFFFFFFFFFFULL, (unsigned long long) z.d.to_uint64() & 0xFFFFFFFFFFULL);
  }
  {
    //    The same in the pair binary32 to bfloat16's layout (8 exponent bits, 7 fraction bits), rounding to
    //    nearest: the largest subnormal of binary32 rounds to 2^-126, which is 0080.
    ac_std_float<32, 8> x;
    x.d = 0x007FFFFF;
    ac_std_float<16, 8> y = x.convert<16, AC_RND_CONV>();
    ac_std_float<16, 8> z = x.convert<16, 8, AC_RND_CONV>();     // the general conversion, same formats
    printf("   ac_std_float<32,8> 007fffff -> <16,8>               convert<16,AC_RND_CONV> %04x   convert<16,8,AC_RND_CONV> %04x   (0080 is right)\n",
           (unsigned) y.d.to_uint64() & 0xFFFF, (unsigned) z.d.to_uint64() & 0xFFFF);
  }
  {
    // 2. A wider exponent: ac_std_float<16,4> (11 fraction bits, smallest normal 2^-6) to binary16
    //    (smallest normal 2^-14). 2^-16 is subnormal in both. In binary16 it is 0x0100.
    ac_std_float<16, 4> x;
    x.d = 0x0002;                                                 // 2 x 2^-17 = 2^-16
    ac_std_float<16, 5> y(x);                                     // the constructor: convert<16, 5, AC_RND_CONV>
    ac_std_float<16, 5> z = x.convert<16, 5, AC_TRN_ZERO>();
    printf("2. ac_std_float<16,4> 0002 (2^-16) -> binary16        constructor %04x         AC_TRN_ZERO %04x         (0100 is right)\n",
           (unsigned) y.d.to_uint64() & 0xFFFF, (unsigned) z.d.to_uint64() & 0xFFFF);
    x.d = 0x0001;                                                 // 2^-17, binary16 0x0080
    ac_std_float<16, 5> w(x);
    printf("   ac_std_float<16,4> 0001 (2^-17) -> binary16        constructor %04x                                  (0080 is right)\n",
           (unsigned) w.d.to_uint64() & 0xFFFF);
  }
  {
    // 3. From an integer with ties to odd: 2^32 - 1 into binary32. It is above the midpoint of its two
    //    neighbours, so every round-to-nearest mode gives 2^32, 4f800000.
    ac_int<32, false> n = 0xFFFFFFFFu;
    ac_std_float<32, 8> a, b;
    a.d = 0;
    b.d = 0;
    a.assign_from<AC_RND_CONV>(n);
    b.assign_from<AC_RND_CONV_ODD>(n);
    printf("3. 4294967295 -> binary32                             AC_RND_CONV %08x   AC_RND_CONV_ODD %08x   (4f800000 is right)\n",
           (unsigned) a.d.to_uint64(), (unsigned) b.d.to_uint64());
    ac_fixed<8, 4, false> f = 7.9375;                             // 127/16 into ac_std_float<8,3>, which has 4 fraction bits
    ac_std_float<8, 3> c;
    c.d = 0;
    c.assign_from<AC_RND_CONV_ODD>(f);
    printf("   7.9375 -> ac_std_float<8,3>                        AC_RND_CONV_ODD %02x                              (60, which is 8.0, is right)\n",
           (unsigned) c.d.to_uint64() & 0xFF);
  }
  return 0;
}
