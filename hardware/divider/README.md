# udiv · unsigned divider

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

## Use

```verilog
udiv #(.WIDTH(32)) u (.a(a), .b(b), .q(q), .r(r));
```

## Proof

```sh
sh prove.sh 10
```

Yosys's SAT solver proves `udiv` equal to `/` and `%` for every `a` and every `b > 0`, and its `b = 0` outputs, at each width from 1 to 10. Widths 16, 32 and 64 are simulated against the operators.
The recurrence and its three-line argument are in the header of `../multiplier/independent_div_checker.py`, which proves the 64-bit LUT netlist row by row.

## Paid evaluation

One arithmetic block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the block as Verilog, the proof files, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on cell count or delay.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

Licence: see `LICENSE.md` at the repository root.
