# IWLS 2025 contest functions ex160 to ex185

The IWLS 2025 programming contest gave 100 new functions, `ex100` to `ex199`, as truth tables and asked for AND-inverter graphs with the fewest nodes.
Four teams entered, and every circuit they submitted is public in [alanminko/iwls2025-ls-contest](https://github.com/alanminko/iwls2025-ls-contest).
The organisers describe `ex160` to `ex179` as two-argument minifloat operations and `ex180` to `ex189` as one-argument half-precision operations.

This folder holds the exact rule for twenty-six of them, down to the rounding of the last bit, and eleven circuits built from the rules.
Each of the eleven is smaller than the smallest of the four teams.

| Function | Operation | Format | Smallest of the four teams, AND nodes | Here, AND nodes | Levels here |
| --- | --- | --- | --- | --- | --- |
| `ex161` | multiply | 8-bit, 1-2-5 | 2,327 | 303 | 36 |
| `ex162` | divide | 8-bit, 1-2-5 | 2,850 | 554 | 140 |
| `ex163` | hypotenuse | 8-bit, 1-2-5 | 2,073 | 678 | 114 |
| `ex165` | add | 8-bit, 1-3-4 | 908 | 368 | 52 |
| `ex166` | multiply | 8-bit, 1-3-4 | 1,347 | 371 | 50 |
| `ex167` | divide | 8-bit, 1-3-4 | 1,328 | 580 | 111 |
| `ex168` | hypotenuse | 8-bit, 1-3-4 | 668 | 646 | 118 |
| `ex170` | add | 8-bit, 1-4-3 | 653 | 368 | 66 |
| `ex180` | 1 / x | half precision | 2,632 | 1,129 | 269 |
| `ex183` | x^2 | half precision | 2,245 | 686 | 64 |
| `ex185` | square root | half precision | 2,277 | 642 | 137 |

"Smallest of the four teams" is the lowest AND count over `submissions/*/2025/` of the contest repository at commit `defcf35`.
The counts here are `and` and `lev` from ABC `print_stats`.
For the other fifteen functions the contest has smaller circuits than this construction gives.

## The 8-bit formats, ex160 to ex179

A number is a sign bit, EB exponent bits and MB mantissa bits. The format 1-2-5 has EB = 2 and MB = 5, and so on.

```
ex160 - ex164    1-2-5        ex165 - ex169    1-3-4        ex170 - ex174    1-4-3        ex175 - ex179    1-5-2
```

Within a format the five functions are add, multiply, divide, hypotenuse and power, in that order.
The 16 inputs are two numbers. Add, multiply and hypotenuse take their first operand from the low byte. Divide and power take it from the high byte: high / low and high ^ low.

```
reading a number                 bias = 2^(EB-1) - 1

exponent field 0                 subnormal: mantissa / 2^MB * 2^(1 - bias), which includes zero
exponent field all ones          infinity, whatever the mantissa
otherwise                        (1 + mantissa / 2^MB) * 2^(exponent - bias)
```

```
writing a result

invalid                          sign 1, exponent all ones, mantissa 0
                                 (0 * inf, inf - inf, 0 / 0, inf / inf, a negative base with a non-integer power)
2^(all ones - bias) and above    infinity with the sign of the result
otherwise                        nearest number of the format, ties away from zero
under one subnormal unit         rounded to one significant bit first: 3/4 of a unit and more gives one unit, less gives zero
```

A zero product or quotient has the exclusive-or of the operand signs. A zero sum is negative when both operands are negative zeros and positive otherwise.
Power follows the special cases of the C library's `pow`: x^0 = 1 and 1^y = 1 for every operand, (-1)^inf = 1, and a negative base with an odd integer power gives a negative result.

The last rule of the table is the unusual one. A result of 0.74 units is written as zero and a result of 0.75 units as one unit, where rounding to nearest would turn at 0.5.

## Half precision, ex180 to ex185

```
ex180  1 / x        ex181  1 / x^2      ex182  1 / x^3      ex183  x^2      ex184  x^3      ex185  sqrt(x)
```

Input and output are IEEE 754 binary16 with subnormals. Each function is the exact real value rounded once, to nearest with ties to even.
A NaN operand comes back with its quiet bit set. The square root of a negative number is the NaN `fe00`, and the square root of -0 is -0.

## The circuits

For the 8-bit formats each operand becomes an integer on the grid of the format's smallest subnormal: the significand shifted left by its exponent.
The exact result is one integer: a sum or a difference, a product, a quotient with enough fraction bits, or the root of a sum of two squares.
One stage, the same for every operation, finds the leading one, rounds, applies the rule under one unit and turns overflow into infinity.
Rounding with ties away from zero reads one bit under the kept significand and nothing below it, so the divider needs no remainder.

The adder of `ex170` shifts the larger operand over the smaller one by the exponent difference, at most six places. Past that distance the smaller operand cannot change the rounded result, and the larger one is the answer. The datapath is eleven bits wide whatever the exponent range.
The hypotenuses of `ex163` and `ex168` do the same with a distance of one and two places.

The half-precision circuits are a significand datapath and a small exponent path. `ex183` squares the 11-bit significand. `ex185` normalises a subnormal operand and takes thirteen root bits. `ex180` divides 2^23 by the significand. One rounding stage, shared by the three, shifts a subnormal result into place and rounds to even.

ABC then reduces the AND count of every circuit.

## Check

[`minifloat.py`](minifloat.py) and [`half.py`](half.py) hold the rules as Python, in exact rational arithmetic. A power that is irrational is taken to 60 digits.
[`check.py`](check.py) compares every rule and every circuit with the contest truth tables on every input. It needs Python only.

```
python3 check.py <folder with ex160.truth ... ex185.truth>
```

```
ex161  mul   1-2-5  rule: 0 of 65536 inputs differ   circuit, 303 AND nodes: 0 of 65536 inputs differ
```

The same check runs on each change to this folder, against the truth tables of contest commit `defcf35` ([workflow](../../../.github/workflows/iwls-2025.yml), checksums in [`truth.sha256`](truth.sha256)).

One circuit against its truth table, in ABC:

```
abc -c "read_aiger ex161.aig; print_stats; &get; &cec -t ex161.truth"
```

## Files

`ex161.aig` and the ten others are binary AIGER, inputs and outputs in the order of the truth tables.
The truth tables are `benchmarks/2025/` in the contest repository.
