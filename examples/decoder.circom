pragma circom 2.0.0;

// One-hot decoder in the style of circomlib's Decoder. For an in-range inp,
// (out[inp], success) can be (1, 1) or (0, 0). Broken. circomlib's
// Multiplexer adds `success === 1`, which removes the second solution.
template Decoder(w) {
    signal input inp;
    signal output out[w];
    signal output success;
    var lc = 0;
    for (var i = 0; i < w; i++) {
        out[i] <-- (inp == i) ? 1 : 0;
        out[i] * (inp - i) === 0;
        lc = lc + out[i];
    }
    lc ==> success;
    success * (success - 1) === 0;
}

component main = Decoder(4);
