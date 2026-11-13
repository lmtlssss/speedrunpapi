# EPFL sin

`sin` is one of the ten arithmetic circuits of the [EPFL combinational benchmark suite](https://github.com/lsils/benchmarks): 24 inputs, 25 outputs, 5,416 AND nodes.
The suite keeps a list of the smallest known LUT-6 implementations.

| | LUT-6 | Levels |
| --- | --- | --- |
| Smallest published, `best_results/size/sin_size_2026.blif` | 994 | 115 |
| [`sin_size_2027.blif`](sin_size_2027.blif) | 685 | 63 |

The counts are `nd` and `lev` from ABC `print_stats`. The netlist gives the benchmark's output on all 16,777,216 inputs.

## What the benchmark computes

The circuit has no description beyond its name. It computes this, for the input word a with bit 0 the first input:

```
q    = a >> 22            b = a mod 2^22
y    = b if q is odd, else (-b) mod 2^22
A    = y >> 15            Z = y mod 2^15            Zm = Z >> 3

core = (C0[A] * 2^14 + (C1[A] - ((K[A] * Zm) >> 12)) * Z + 2^16) >> 17
core = 2^23 when q is even and b = 0

out  = core for q = 0 and 3, -core for q = 1 and 2          25 bits, two's complement
```

`C0`, `C1` and `K` are tables of 128 entries in [`tables.json`](tables.json): `C0` has 26 bits, `C1` 19 bits, `K` 12 bits.

The value is 2^23 · cos(2π · a / 2^24). The argument is folded onto a quarter wave, the quarter wave is cut into 128 segments, and each segment is a second-order polynomial in Horner form with two truncations.
`C0[A]` is the sine at the start of segment A with three fraction bits, `C1[A]` the slope with 17 fraction bits, `K[A]` the curvature.
The benchmark equals the cosine rounded to nearest on 15,613,364 inputs and is one off on the other 1,163,852.

## The netlist

It is built from the formula: the fold of the argument, the three tables, radix-4 rows for the two products, and one LUT per bit in every addition, with the carry recovered from the column below.
A row is a radix-4 digit times its multiplicand, one LUT per bit. A digit of 3 needs the multiplicand plus twice itself; the row bit takes that carry from the row bit below it, so no adder forms the triple.
In the two additions whose low bits are thrown away, the columns under the cut pass their carries upward and form no sum bit.
That is 717 LUTs. ABC `mfs2`, `lutpack` and `&satlut` then took it to 685.

## Check

[`check.py`](check.py) evaluates the benchmark, the formula and the netlist on every input and counts the inputs where they differ. It needs Python with numpy and takes about 20 seconds.

```
python3 check.py <arithmetic/sin.aig of lsils/benchmarks>
```

```
formula: 0 of 16777216 inputs differ from the benchmark
netlist: 685 nodes, at most 6 inputs each, 0 of 16777216 inputs differ from the benchmark
benchmark against the cosine rounded to nearest: equal on 15613364 inputs, one off on 1163852, further off on 0
```

The same check runs on each change to this folder against `sin.aig` of lsils/benchmarks commit `82d8cc6` ([workflow](../../.github/workflows/epfl-sin.yml)).
