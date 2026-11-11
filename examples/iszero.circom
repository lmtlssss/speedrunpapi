pragma circom 2.0.0;

// out is 1 when in is 0, else 0. inv is a hint: it is free when in = 0,
// yet out is fixed in both cases. Certified, by case analysis on in.
template IsZero() {
    signal input in;
    signal output out;
    signal inv;
    inv <-- in != 0 ? 1 / in : 0;
    out <== -in * inv + 1;
    in * out === 0;
}

component main = IsZero();
