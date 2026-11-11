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

// sum is range-checked but carry is not: for any n-bit sum,
// carry = (a + b - sum) / 2^n satisfies the equation. Broken.
template ModSum(n) {
    signal input a;
    signal input b;
    signal output sum;
    signal output carry;
    carry <-- (a + b) >> n;
    sum <-- (a + b) - carry * (1 << n);
    component rc = Bits(n);
    rc.in <== sum;
    a + b === sum + carry * (1 << n);
}

component main = ModSum(4);
