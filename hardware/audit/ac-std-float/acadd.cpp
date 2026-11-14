// ac_std_float<W,E>::add on 1.0 + y for negative y so small that the sum must round back to 1.0.
// y runs over every exponent from 2^-(M+3) down to 2^-(M+10) and over significands (all of them when the
// format has 13 fraction bits or fewer, 4,096 drawn ones otherwise), M being the number of fraction bits.
// |y| is below a quarter of the last place of 1.0, which is half of the last place just under 1.0, so in every
// round-to-nearest mode the answer is 1.0 itself.
#include <ac_std_float.h>
#include <cstdint>
#include <cstdio>

static uint64_t seed = 88172645463325252ULL;
static uint64_t rnd() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; }

template<int W, int E, ac_q_mode QR>
static long count(const char *mode, bool show) {
  typedef ac_std_float<W, E> F;
  const int M = W - E - 1;
  const int bias = (1 << (E - 1)) - 1;
  F one, y, r;
  one.d = 0;
  one.d.set_slc(M, ac_int<E, false>(bias));
  long wrong = 0, total = 0;
  for (int k = M + 3; k <= M + 10 && k < bias; k++) {   // y stays a normal number
    long n = M <= 13 ? (1L << M) : 4096;
    for (long i = 0; i < n; i++) {
      ac_int<M, false> frac = M <= 13 ? ac_int<M, false>(i) : ac_int<M, false>((unsigned long long) rnd());
      y.d = 0;
      y.d.set_slc(0, frac);
      y.d.set_slc(M, ac_int<E, false>(bias - k));
      y.d[W - 1] = true;
      r = one.template add<QR, false>(y);
      total++;
      if (r.d != one.d) {
        wrong++;
        if (show && wrong == 1)
          printf("  ac_std_float<%d,%d> %s: 1.0 + (%s) = %s, not %s\n", W, E, mode,
                 y.d.to_string(AC_HEX, false, true).c_str(), r.d.to_string(AC_HEX, false, true).c_str(),
                 one.d.to_string(AC_HEX, false, true).c_str());
      }
    }
  }
  printf("ac_std_float<%d,%d>, %d fraction bits, %s: %ld of %ld sums are not 1.0\n", W, E, M, mode, wrong, total);
  return wrong;
}

template<int W, int E>
static void all() {
  count<W, E, AC_RND_CONV>("AC_RND_CONV", true);
  count<W, E, AC_RND_INF>("AC_RND_INF", false);
  count<W, E, AC_RND_CONV_ODD>("AC_RND_CONV_ODD", false);
}

int main() {
  all<12, 6>();      // 5 fraction bits
  all<20, 6>();      // 13
  all<24, 10>();     // 13
  all<40, 10>();     // 29
  all<72, 10>();     // 61
  all<16, 5>();      // binary16, 10
  all<32, 8>();      // binary32, 23
  all<64, 11>();     // binary64, 52
  all<16, 8>();      // bfloat16, 7
  all<19, 6>();      // 12, a neighbour
  all<21, 6>();      // 14, a neighbour
  return 0;
}
