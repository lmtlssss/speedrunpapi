# Arithmetic compilers

Builds `a * b`, `a * a`, `a / b` with remainder, `floor(sqrt(a))` and `floor(sqrt(a*a + b*b))` as 6-input LUT networks, with proofs.

## Method

Split each operand in two. `X*Y = Z0 + 2^(2h) Z2 + 2^h (P - Z0 - Z2)`, with `P = (Xl + Xh)(Yl + Yh)`.
`Z0` and `Z2` are kept as words and read twice. The second reading is negated inside the LUT that consumes it.
Leaves are unsigned radix-4 rows over `X`, `2X` and one shared `3X` word. Squares fold `x_i x_j` and `x_j x_i` into one term.
Every addition is one LUT per bit. The carry into a column is recovered from the previous column's wires and its sum bit, so no carry wire exists.
Each block size is built as a leaf and as a split; the smaller network is kept.

Square root: non-restoring rows `r' = 4r + pair + 3 + 4 (Q xnor s)`, with `s` the sign of `r`. One expression covers the add row and the subtract row, and each bit of a row is one LUT. The top LUT of a row emits the root bit. The last row builds carries only.
Hypotenuse: two squarers, one addition, then the square-root rows.
Depth builds (`mul_depth.py`): level 1 is the recoded row bits, or three folded products per counter for the squarer. Counters then cut every column to a common target height per level, so no carry waits for a later level. The last stage is a radix-3 prefix adder whose final carry combine sits inside the sum LUTs.
Fold divider (`div_fold.py`): the divisor is normalised and a table value `M` puts `D = M * dn` just below a power of two, `eps = 2^P - D`. The top field `T` of the running value then folds back as `T * eps`, because `T * 2^P = T * D + T * eps`. The value stays in two rows and `T` is their pair of top fields, read as radix-4 digits of `eps` and `3 eps`: one fold is 4 LUT levels and retires 8 quotient bits, with no digit selection inside the loop. `a - Q * b` runs in a second heap on the same fields and ends below `3b`.
Divider: non-restoring rows on a growing word. Row `j` keeps the remainder mod `2^(j+1)`; its sign is `[b >= 2^j]` or the top bit. A 64-bit divider uses 2,144 row LUTs where a full-width array uses 4,160.

## Results

Counts are ABC `print_stats` on LUT-6 netlists. Reference: EPFL arithmetic benchmarks, lsils/benchmarks best size results, 2026.

| Benchmark | EPFL best size | This compiler | Netlist |
| --- | --- | --- | --- |
| `multiplier`, 64 x 64 | 4282 LUT-6, 229 levels | 3654 LUT-6, 131 levels | `epfl/multiplier.blif` |
| `square`, 64-bit | 2894 LUT-6, 192 levels | 2497 LUT-6, 127 levels | `epfl/square.blif` |
| `sqrt`, 128-bit | 2958 LUT-6 | 2174 LUT-6 | `epfl/sqrt.blif` |
| `hyp`, 128-bit sides | 36451 LUT-6 | 24898 LUT-6 | `epfl/hyp.blif.gz` |
| `div`, 64 / 64 | 3082 LUT-6 | 2287 LUT-6 | `epfl/div.blif` |

Depth builds, against the EPFL best depth results:

| Benchmark | EPFL best depth | This compiler | Netlist |
| --- | --- | --- | --- |
| `multiplier`, 64 x 64 | 25 levels, 6381 LUT-6 | 11 levels, 5178 LUT-6 | `epfl/multiplier_depth.blif` |
| `square`, 64-bit | 10 levels, 3690 LUT-6 | 10 levels, 3358 LUT-6 | `epfl/square_depth.blif` |
| `div`, 64 / 64 | 170 levels, 30849 LUT-6 | 58 levels, 20232 LUT-6 | `epfl/div_depth.blif.gz` |

## Run

```sh
python3 mul_compiler.py --n 64 --out out/
python3 mul_compiler.py --n 64 --square --out out/
python3 independent_mul_checker.py --netlist epfl/multiplier.blif --derivation epfl/multiplier.derivation.json
python3 independent_mul_checker.py --netlist epfl/square.blif --derivation epfl/square.derivation.json
python3 sqrt_compiler.py --m 64 --out out/
python3 hyp_compiler.py --n 128 --out out/
python3 independent_sqrt_checker.py --netlist epfl/sqrt.blif --derivation epfl/sqrt.derivation.json
gunzip -k epfl/hyp.blif.gz epfl/hyp.derivation.json.gz
python3 independent_sqrt_checker.py --netlist epfl/hyp.blif --derivation epfl/hyp.derivation.json
python3 div_compiler.py --n 64 --out out/
python3 mul_depth.py --n 64 --out out/ && python3 mul_depth.py --n 64 --square --out out/
python3 independent_depth_checker.py --netlist epfl/multiplier_depth.blif --derivation epfl/multiplier_depth.derivation.json
python3 independent_div_checker.py --netlist epfl/div.blif --derivation epfl/div.derivation.json
python3 div_fold.py --n 64 --b 8 --out out/
gunzip -k epfl/div_depth.blif.gz epfl/div_depth.derivation.json.gz
python3 independent_fold_checker.py --netlist epfl/div_depth.blif --derivation epfl/div_depth.derivation.json
lean FoldDivision.lean
python3 test_mul.py && python3 test_sqrt.py && python3 test_div.py && python3 test_depth.py && python3 test_fold.py
```

## Proof

`independent_mul_checker.py` shares no code with the compiler. The derivation names blocks: which LUTs belong together, which earlier words a block reads, and the word expression it computes.

1. For each block the checker writes `sum 2^c out_c` as a polynomial, replaces every LUT by the polynomial of its truth table, and reduces coefficients mod `2^width`. The result must equal the block's expression over its operand wires.
2. Each expression is carried as an integer polynomial in word variables. Its range must lie inside the word.
3. The last word is the output vector. Its polynomial must be `a*b`.

The 64 x 64 multiplier checks in 0.5 s and the 64-bit squarer in 0.3 s on an Apple M1.
`independent_sqrt_checker.py` proves the square root and the hypotenuse. Its header states the recurrence and the three-line argument that it yields `Q^2 <= X < (Q+1)^2`. For each row it rebuilds the row's polynomial from the netlist and compares it with the recurrence; for the hypotenuse it first proves the radicand word equals `(a*a + b*b) mod 2^256` by the block replay above. Run time: 0.3 s and 6 s.
`test_sqrt.py` checks the recurrence against `isqrt` for every operand up to 18 bits, simulates small circuits exhaustively and removes minterms one at a time.

`independent_div_checker.py` proves the divider the same way: every row's polynomial equals the recurrence in its header, every quotient LUT is the stated NOR over `b_j .. b_63`, and the remainder row equals `r + s*b`. `test_div.py` checks the recurrence against integer division for every operand pair up to 8 bits.

`independent_depth_checker.py` proves the depth builds in two steps: the two rows left by the counters sum to `a*b` (polynomial identity rebuilt from the netlist), and the final adder equals a ripple adder of those rows (ABC `cec`). Under one second each; needs `yosys-abc` on the path.

`independent_fold_checker.py` proves the fold divider from the netlist: the leading-zero count against a counter (ABC `cec`); every shifter LUT as a 4:1 select; the table on all 2,048 readings, with `0 <= 2^75 - M * dn < 2^65` for every `dn` under each reading; each heap as a polynomial identity over its wires, exact for the folds; each adder against a ripple adder (ABC `cec`); the bound `W' < 3 * 2^p` after each fold; the output selection. 4 s for 64 bits. `FoldDivision.lean` proves the fold step, the bound, `Q*b <= a < Q*b + 3b` after the last field and the selection among `R, R - b, R - 2b` for all integers. `test_fold.py` checks 8- and 9-bit builds on every input and removes minterms one at a time: 120 altered netlists, none accepted with a wrong result.

The two recurrences themselves are proved in Lean 4 for every width, core library only: `GrowingWordDivision.lean` (`Colony.div_correct`: the rows return `a / b` and `a % b`; `Colony.div_zero`) and `RetainedSignSqrt.lean` (`Colony.sqrt_correct`: `Q*Q <= X < (Q+1)*(Q+1)`). Run `lean GrowingWordDivision.lean`; each checks in under three seconds. The netlist checkers prove every row equals its recurrence, and these files prove the recurrence.

`test_mul.py` runs exhaustive simulation at small widths and removes minterms one at a time: 191 altered 8-bit netlists, none accepted with a wrong product.

## Paid evaluation

One arithmetic block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the LUT netlist as Verilog, the proof files with the independent checker, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on LUT count or logic depth.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

Python 3.9+, standard library only. Licence: see `LICENSE.md` at the repository root.
