pragma circom 2.0.0;
template Compare() {
  signal input a;
  signal input b;
  signal output out;
  signal diff;
  signal bit[5];
  diff <== a + 16 - b;
  var lc = 0;
  var e2 = 1;
  for (var i=0; i<5; i++) {
    bit[i] <-- (diff >> i) & 1;
    bit[i] * (bit[i] - 1) === 0;
    lc += bit[i] * e2;
    e2 = e2 + e2;
  }
  lc === diff;
  out <== 1 - bit[4];
}
component main {public [a,b]} = Compare();
