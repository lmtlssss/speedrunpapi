# udiv, udivf · unsigned dividers

`udiv.v`: `q = a / b`, `r = a % b`, combinational, any `WIDTH`. `b = 0` gives `q` = all ones and `r = a`.

## Method

Non-restoring division on a growing word. Stage `j` keeps the partial remainder modulo `2^(j+1)`.
Its sign is the top bit of that word, or 1 when `b >= 2^j`: `b` then exceeds the `j` bits of `a` read so far.
When `b < 2^j` the remainder lies in `[-2^j, 2^j)` and the word holds it exactly.
Stage `j` is one `(j+1)`-bit adder.

## Results

Against the Verilog operators `/` and `%` in one module, Yosys 0.70.

Lattice ECP5, placed and routed (`synth_ecp5` + nextpnr-ecp5, best of 3 seeds, register to register):

| Width | `/` and `%` | `udiv` |
| --- | --- | --- |
| 16 | 57.5 ns, 583 cells | 53.4 ns, 493 cells |
| 32 | 139.7 ns, 2196 cells | 121.8 ns, 1417 cells |
| 64 | 393.7 ns, 12246 cells | 292.4 ns, 4889 cells |

Xilinx 7-series, synthesis (`synth_xilinx`):

| Width | `/` and `%` | `udiv` |
| --- | --- | --- |
| 16 | 279 LUT, 100 CARRY4 | 197 LUT, 47 CARRY4 |
| 32 | 1079 LUT, 392 CARRY4 | 664 LUT, 159 CARRY4 |
| 64 | 4215 LUT, 1552 CARRY4 | 2352 LUT, 575 CARRY4 |

The LUT-only form of the same recurrence is the EPFL `div` netlist in `../multiplier/` at 2287 LUT-6; the published best is 3082.

## udivf

`udivf32.v`, `udivf64.v`: the same function at lower delay. `python3 udivf_gen.py WIDTH > udivfWIDTH.v` writes any width from 12 bits.

Normalise the divisor: `dn = b << lzc(b)`. A table read from the top 12 bits of `dn` gives `m` with `m * dn` in `(2^P - 2^(P-10), 2^P]`. Let `eps = 2^P - m * dn`.
`t * 2^P = t * (m * dn) + t * eps`. The top field `t` of the running value `m * a << lzc(b)` is removed and `t * eps` is added: 8 quotient bits per step.
The quotient is the sum of the fields. `a - q * b` lies in `[0, 3b)` and selects the result.

Lattice ECP5, placed and routed, same flow:

| Width | `/` and `%` | `udiv` | `udivf` |
| --- | --- | --- | --- |
| 32 | 139.7 ns, 2196 cells | 121.8 ns, 1417 cells | 87.0 ns, 2950 cells, 15 MULT18X18D |
| 64 | 393.7 ns, 12246 cells | 292.4 ns, 4889 cells | 181.2 ns, 5161 cells, 49 MULT18X18D |

Intel Cyclone V `5CGXFC9E7F35C8`, Quartus Prime Lite 21.1.1, map, fit and timing analysis at default effort, register to register, slow corner, 64 bits:

| | Delay | ALMs | DSP blocks |
| --- | --- | --- | --- |
| `/` and `%` | 248.1 ns | 5094 | 0 |
| `udiv` | 261.1 ns | 1350 | 0 |
| `udivf64` | 159.7 ns | 1866 | 35 |

`sh prove_udivf.sh` proves `udivf` equal to `/` and `%` at widths 8, 10 and 12 (steps of 2, 3 and 4 bits) with Yosys's SAT solver. Widths 16, 32 and 64 are simulated against the operators on 3,000 vectors each.
`../multiplier/FoldDivision.lean` proves the step, the bound on the running value and the final selection for every width.

## Use

```verilog
udiv #(.WIDTH(32)) u (.a(a), .b(b), .q(q), .r(r));
udivf64 f (.a(a), .b(b), .q(q), .r(r));
```

## Proof

```sh
sh prove.sh 10
```

Yosys's SAT solver proves `udiv` equal to `/` and `%` for every `a` and every `b > 0`, and its `b = 0` outputs, at each width from 1 to 10. Widths 16, 32 and 64 are simulated against the operators.
`GrowingWordDivision.lean` proves the recurrence for every width in Lean 4, core library only: `Colony.div_correct` states that for `0 < b <= 2^n` the rows return `a / b` and the remainder word is `a % b`. Run `lean GrowingWordDivision.lean`.

## Paid evaluation

One arithmetic block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the block as Verilog, the proof files, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on cell count or delay.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

Licence: see `LICENSE.md` at the repository root.
