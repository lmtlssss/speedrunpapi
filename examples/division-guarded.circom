pragma circom 2.0.0;

// The same division with b forced to be invertible. Certified.
template DivisionGuarded() {
    signal input a;
    signal input b;
    signal output q;
    signal binv;
    binv <-- b != 0 ? 1 / b : 0;
    binv * b === 1;
    q <-- a * binv;
    q * b === a;
}

component main = DivisionGuarded();
