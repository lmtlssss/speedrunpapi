pragma circom 2.0.0;

// 254 bits over BN254: 2^254 exceeds the modulus, so in and in + p have
// different decompositions. Broken. circomlib guards this with Num2Bits_strict.
template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc = 0;
    var e2 = 1;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] - 1) === 0;
        lc += out[i] * e2;
        e2 = e2 + e2;
    }
    lc === in;
}

component main = Num2Bits(254);
