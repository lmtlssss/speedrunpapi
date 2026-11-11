pragma circom 2.0.0;

template Bits(n) {
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

// a + b is decomposed into n + 1 bits; sum and carry are read off those
// bits. Certified.
template ModSum(n) {
    signal input a;
    signal input b;
    signal output sum;
    signal output carry;
    component d = Bits(n + 1);
    d.in <== a + b;
    var lc = 0;
    var e2 = 1;
    for (var i = 0; i < n; i++) {
        lc += d.out[i] * e2;
        e2 = e2 + e2;
    }
    sum <== lc;
    carry <== d.out[n];
}

component main = ModSum(4);
