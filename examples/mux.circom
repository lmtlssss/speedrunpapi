pragma circom 2.0.0;
template Choice() {
  signal input a;
  signal input b;
  signal input s;
  signal output out;
  out <== (b-a)*s+a;
}
component main {public [a,b,s]} = Choice();
