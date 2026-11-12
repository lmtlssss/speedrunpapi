# Multiplier and squarer compiler

Builds `a * b` and `a * a` as 6-input LUT networks, with a proof.

## Method

Split each operand in two. `X*Y = Z0 + 2^(2h) Z2 + 2^h (P - Z0 - Z2)`, with `P = (Xl + Xh)(Yl + Yh)`.
`Z0` and `Z2` are kept as words and read twice. The second reading is negated inside the LUT that consumes it.
Leaves are unsigned radix-4 rows over `X`, `2X` and one shared `3X` word. Squares fold `x_i x_j` and `x_j x_i` into one term.
Every addition is one LUT per bit. The carry into a column is recovered from the previous column's wires and its sum bit, so no carry wire exists.
Each block size is built as a leaf and as a split; the smaller network is kept.

## Results

Counts are ABC `print_stats` on LUT-6 netlists. Reference: EPFL arithmetic benchmarks, lsils/benchmarks best size results, 2026.

| Benchmark | EPFL best size | This compiler | Netlist |
| --- | --- | --- | --- |
| `multiplier`, 64 x 64 | 4282 LUT-6, 229 levels | 3654 LUT-6, 131 levels | `epfl/multiplier.blif` |
| `square`, 64-bit | 2894 LUT-6, 192 levels | 2497 LUT-6, 127 levels | `epfl/square.blif` |

## Run

```sh
python3 mul_compiler.py --n 64 --out out/
python3 mul_compiler.py --n 64 --square --out out/
python3 independent_mul_checker.py --netlist epfl/multiplier.blif --derivation epfl/multiplier.derivation.json
python3 independent_mul_checker.py --netlist epfl/square.blif --derivation epfl/square.derivation.json
python3 test_mul.py
```

## Proof

`independent_mul_checker.py` shares no code with the compiler. The derivation names blocks: which LUTs belong together, which earlier words a block reads, and the word expression it computes.

1. For each block the checker writes `sum 2^c out_c` as a polynomial, replaces every LUT by the polynomial of its truth table, and reduces coefficients mod `2^width`. The result must equal the block's expression over its operand wires.
2. Each expression is carried as an integer polynomial in word variables. Its range must lie inside the word.
3. The last word is the output vector. Its polynomial must be `a*b`.

The 64 x 64 multiplier checks in 0.5 s and the 64-bit squarer in 0.3 s on an Apple M1.
`test_mul.py` runs exhaustive simulation at small widths and removes minterms one at a time: 191 altered 8-bit netlists, none accepted with a wrong product.

## Paid evaluation

One arithmetic block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the LUT netlist as Verilog, the proof files with the independent checker, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on LUT count or logic depth.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

Python 3.9+, standard library only. Licence: see `LICENSE.md` at the repository root.
