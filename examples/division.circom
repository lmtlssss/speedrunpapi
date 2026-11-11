pragma circom 2.0.0;

// q is a hint for a / b, checked by q * b === a. When a = b = 0 the check
// holds for every q. Broken.
template Division() {
    signal input a;
    signal input b;
    signal output q;
    q <-- b != 0 ? a / b : 0;
    q * b === a;
}

component main = Division();
