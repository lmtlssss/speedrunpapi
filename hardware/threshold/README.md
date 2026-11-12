# Threshold-count compiler

Builds `maj = [popcount(A[0..n-1]) >= T]` as a k-input LUT network, with a proof.

Uses: k-of-n voters, sync-word and preamble detectors with an error allowance, 1-bit correlators, binarised-network neurons.

## Method

Add the constant `2^m - T`. The answer is bit `m` of `popcount + constant`; no comparator is built.
Reduce the bit heap with counters of at most `k` inputs, one LUT per digit.
Only carries cross a column cut. The residue of a cleared column is never observed, so it is never computed.

## Results

Counts are ABC `print_stats` on LUT-6 netlists. Reference: EPFL `voter` (1001-input majority), lsils/benchmarks `82d8cc6910`.

| Netlist | LUT-6 | Levels | Evidence |
| --- | --- | --- | --- |
| EPFL best size, 2026 | 1145 | 33 | published |
| EPFL best depth, 2026 | 1325 | 11 | published |
| `epfl-voter/voter_size_987.blif` | 987 | 12 | derivation replay; Lean kernel proof |
| `epfl-voter/voter_size_991.blif` | 991 | 14 | 12 chained ABC `cec` steps from the original |
| `epfl-voter/voter_depth_1005.blif` | 1005 | 9 | ABC-equivalent to `voter_depth.blif`, which has a Lean kernel proof |

Submitted to the EPFL suite on 2026-11-11.

Placed and routed on Lattice ECP5 (Yosys `synth_ecp5` + nextpnr-ecp5, best of 3 seeds, register to register). The baseline is behavioural RTL, free to use carry chains.

| Inputs, T | Baseline | This compiler (`--k 4 --objective depth`) |
| --- | --- | --- |
| 36, 32 | 7.61 ns, 155 cells | 6.62 ns, 70 cells |
| 64, 56 | 12.87 ns, 271 cells | 8.76 ns, 139 cells |
| 127, 64 | 12.20 ns, 557 cells | 10.57 ns, 296 cells |
| 255, 160 | 16.62 ns, 1079 cells | 13.87 ns, 664 cells |

## Choosing a build

| Target | Option |
| --- | --- |
| FPGA, lowest latency | `--objective depth` |
| FPGA, fewest LUTs | `--objective size` |
| Standard cells | `--k 3` |
| ABC `cec` against an existing netlist | `--tree`, then `abc_chain.py` |

## Run

```sh
python3 threshold_compiler.py --n 64 --threshold 56 --objective depth --out out/
python3 independent_threshold_checker.py --netlist out/threshold.blif --derivation out/derivation.json
python3 lean_proof.py --netlist out/threshold.blif --derivation out/derivation.json --out out/proof.lean && lean out/proof.lean
python3 test_threshold.py
```

## Paid evaluation

One block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the LUT netlist as Verilog, the proof files with the independent checker, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on LUT count or logic depth.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

## Proof

Three checks, sharing no code:

1. `independent_threshold_checker.py` replays the derivation: every node identity on all rows, then integer bookkeeping.
2. `lean_proof.py` emits a Lean 4 file (core Lean, no Mathlib) ending in
   `theorem correct (x : Nat → Bool) : w_maj x = decide (popcount x n ≥ T)`.
   All three 1001-input voter netlists have one, checked by Lean 4.33.1 on an Apple M1:
   `epfl-voter/voter_size.lean` (993 LUT-6) in 26 s, `epfl-voter/voter_depth.lean` (9 levels) in 91 s, `epfl-voter/voter_size_987.lean` (987 LUT-6) in 105 s.
   Run `lean epfl-voter/voter_depth.lean`.
3. `bdd_threshold_check.cpp` compares canonical BDDs without any certificate. Completes for n up to 127.

Python 3.9+, standard library only. Licence: see `LICENSE.md` at the repository root.
