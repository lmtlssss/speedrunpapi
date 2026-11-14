// The library's own quantization and overflow: every value of ac_fixed<7,4,true> (three fraction bits) assigned to
// ac_fixed<3,3,true,Q,O> and ac_fixed<3,3,false,Q,O> for each of the eight quantization modes and two overflow
// modes. One line per assignment: mode index, overflow index, signed flag, source raw bits, result raw bits.
// acq.py compares each line with the definitions used in acm.py.
#include <ac_fixed.h>
#include <cstdio>

template<ac_q_mode Q, ac_o_mode O, bool S>
static void run(int q, int o) {
  for (unsigned v = 0; v < 128; v++) {
    ac_fixed<7, 4, true> x;
    x.set_slc(0, ac_int<7, false>(v));
    ac_fixed<3, 3, S, Q, O> y = x;
    printf("%d %d %d %x %llx\n", q, o, (int) S, v, (unsigned long long) y.template slc<3>(0).to_uint64() & 7);
  }
}

template<ac_q_mode Q>
static void modes(int q) {
  run<Q, AC_WRAP, true>(q, 0);
  run<Q, AC_SAT, true>(q, 1);
  run<Q, AC_WRAP, false>(q, 0);
  run<Q, AC_SAT, false>(q, 1);
}

int main() {
  modes<AC_TRN>(0);
  modes<AC_TRN_ZERO>(1);
  modes<AC_RND>(2);
  modes<AC_RND_ZERO>(3);
  modes<AC_RND_INF>(4);
  modes<AC_RND_MIN_INF>(5);
  modes<AC_RND_CONV>(6);
  modes<AC_RND_CONV_ODD>(7);
  return 0;
}
