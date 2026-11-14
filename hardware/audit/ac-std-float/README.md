# `ac_std_float`

[`ac_std_float.h`](https://github.com/hlslibs/ac_types/blob/085324204357110e11884e8176f713f7b181153f/include/ac_std_float.h) of [hlslibs/ac_types](https://github.com/hlslibs/ac_types), the Algorithmic C datatypes that Siemens publishes for high-level synthesis, at commit `0853242` (Release Build 2026.3.1). `ac_std_float<W,E>` is its floating-point class in the IEEE layout for any total width `W` and exponent width `E`; `ac_ieee_float` and `ac::bfloat16` are built on it. The header is both the simulation model and the source the synthesis tool reads.

The class is run as it is. For a small format, every operand, pair or triple goes through one operation in each of the library's four rounding modes, and every result is compared with [`acref.py`](acref.py): the operation done on fractions of integers and rounded once. For binary32 and binary64 the comparison is with the processor's own arithmetic.

Three things are wrong. Everything else that was run agrees.

## `fma` with ties to odd doubles the result

`fma<AC_RND_CONV_ODD>` returns twice the correct value when the exact result is a tie whose lower neighbour has an all-ones significand.

```
binary32  fma(2^-12, 2^-12, 2 - 2^-23)          exact: 2 - 2^-24, halfway between 3fffffff and 40000000
  AC_RND_CONV      40000000
  AC_TRN_ZERO      3fffffff
  AC_RND_INF       40000000
  AC_RND_CONV_ODD  407fffff                      3fffffff is right; 407fffff is 4 - 2^-22
  mult then add, AC_RND_CONV_ODD  3fffffff

binary64  fma(2^-27, 2^-26, 2 - 2^-52)
  AC_RND_CONV_ODD  400fffffffffffff              3fffffffffffffff is right
```

Every operand triple of two formats:

| format | triples | wrong with ties to odd | wrong in the other three modes |
| --- | --- | --- | --- |
| `ac_std_float<6,3>` | 262,144 | 3,520 | 0 |
| `ac_std_float<7,3>` | 2,097,152 | 10,212 | 0 |

Of the 3,520, 3,024 are twice the right value and 496 are infinity where the largest finite number is right.

Cause. Line 1458 of `fma_generic` decides that the rounding will carry into the next power of two whenever the significand and the round bit are all ones:

```cpp
bool rnd_ovf = (QR != AC_TRN_ZERO) & !add_r[accu_size-1] & (t == t_h(-1));
```

With ties to odd an exact tie stays on the all-ones significand. The exponent is raised anyway and the significand is left as it is. The multiplier has the term that is missing (line 1166: `& ((QR != AC_RND_CONV_ODD) | sticky_bit)`).

## `add` and `sub` at fraction widths 5, 13, 29 and 61

When the fraction `W - E - 1` is 5, 13, 29 or 61 bits wide, `add` and `sub` in the three round-to-nearest modes return the neighbour of the correct result if one operand is far smaller than the other.

```
ac_std_float<20,6>, AC_RND_CONV     1.0 + (0x9E001) = 0x3DFFF      0x9E001 is -(1 + 2^-13) x 2^-16
                                                                    the sum is a quarter of a step below 1.0: 0x3E000 is right
```

[`acadd.cpp`](acadd.cpp) adds to 1.0 every negative y from 2^-(M+3) down to 2^-(M+10), M being the fraction width, over all significands for M up to 13 and 4,096 drawn ones above that:

| format | fraction bits | sums that are not 1.0, AC_RND_CONV |
| --- | --- | --- |
| `ac_std_float<12,6>` | 5 | 248 of 256 |
| `ac_std_float<20,6>` | 13 | 65,528 of 65,536 |
| `ac_std_float<24,10>` | 13 | 65,528 of 65,536 |
| `ac_std_float<40,10>` | 29 | 32,768 of 32,768 |
| `ac_std_float<72,10>` | 61 | 32,768 of 32,768 |
| binary16, binary32, binary64, bfloat16, `<19,6>` (12 bits), `<21,6>` (14 bits) | | 0 |

AC_RND_INF gives the same counts, and AC_RND_CONV_ODD is wrong on every one. The eight right sums in each of the first three rows are the y with a zero fraction, which land on an exact tie.

Every operand pair of `ac_std_float<10,4>`, which has 5 fraction bits: `add` is wrong on 3,024 of 1,048,576 pairs with AC_RND_CONV, 3,024 with AC_RND_INF, 3,136 with AC_RND_CONV_ODD and 0 with AC_TRN_ZERO, and `sub` has the same four counts. Each wrong result is one unit in the last place off.

Cause. `add_generic` shifts the smaller operand right by the exponent difference into a field with three bits below the point: guard, round, sticky. The shift has to reach `mu_bits + 2` before the whole operand is under the sticky bit; `mu_bits` is the fraction width plus one. The difference is saturated first (lines 963 to 966) in a type of `ac::nbits<mu_bits+1>` bits. For most widths that type's largest value is above `mu_bits + 1`. When `mu_bits + 1` is all ones, which is `mu_bits` = 6, 14, 30, 62, it is exactly `mu_bits + 1`. A shift of that much leaves the operand's leading bit in the round position, so an operand any distance away counts as a quarter of a unit in the last place.

## `ceil`, `trunc` and `round` lose the sign of zero

For a negative operand whose result is zero, `ceil`, `trunc` and `round` return +0, and `trunc` and `round` return +0 for -0. `floor` keeps the sign. The C library returns -0, as IEEE 754 does for rounding to an integral value.

```
                   ac_std_float<32,8>    ceilf, truncf, roundf
ceil(-0.5)         00000000              80000000
trunc(-0.5)        00000000              80000000
round(-0.25)       00000000              80000000
trunc(-0)          00000000              80000000
round(-0)          00000000              80000000
```

The library is on both sides of that table. `ac_ieee_float<binary32>` and `<binary64>` call the C functions when `AC_IEEE_FLOAT_USE_BUILTIN` is defined, and the header undefines that macro under `__SYNTHESIS__`. [`acbuiltin.cpp`](acbuiltin.cpp) makes the first three calls through `ac_ieee_float<binary32>`: it prints `00000000` compiled plain and `80000000` compiled with `-DAC_IEEE_FLOAT_USE_BUILTIN`. A simulation built with the builtin and one built without it differ in that bit, and synthesis always takes the second path.

Every operand of four formats:

| format | operands | `ceil` | `trunc` | `round` | `floor` |
| --- | --- | --- | --- | --- | --- |
| `ac_std_float<8,4>` | 256 | 55 | 56 | 48 | 0 |
| `ac_std_float<9,4>` | 512 | 111 | 112 | 96 | 0 |
| `ac_std_float<10,4>` | 1,024 | 223 | 224 | 192 | 0 |
| `ac_std_float<11,4>` | 2,048 | 447 | 448 | 384 | 0 |

Cause. Lines 1688, 1745 and 1764 return `zero()` for these operands.

## The patch

[`ac_std_float.patch`](ac_std_float.patch) is seven lines of code in the header: the missing term in `fma`, one more value in the type of the saturated shift, and `-zero()` in the three functions when the sign bit is set. With it:

- the three reproducers print the right values;
- `fma` on every triple of the 6.3 and 7.3 formats, four rounding modes: 9,437,184 operations, 0 wrong;
- `add`, `sub`, `mult`, `div` and `sqrt` on every operand of the 8.3, 9.4 and 10.4 formats, four rounding modes: 22,027,264 operations, 0 wrong;
- `ceil`, `floor`, `trunc` and `round` on every operand of the four formats above: 0 wrong;
- the table of `acadd.cpp` is 0 in every row and every mode.

## What agrees

The header as published, without the patch:

- `add`, `sub`, `mult`, `div` and `sqrt` on every operand of eight formats (5.2, 6.2, 6.3, 7.2, 7.3, 9.3, 9.4, 10.3; written width.exponent), four rounding modes: 160 runs, 25,847,424 operations, 0 wrong.
- The same five on the 8.3 and 8.4 formats, and `mult`, `div` and `sqrt` on 10.4: 0 wrong.
- `add`, `mult` and `div` on the 11.3 and 11.4 formats, four rounding modes: 100,663,296 operations, 0 wrong.
- `fma` with AC_RND_CONV, AC_TRN_ZERO and AC_RND_INF on every triple of 6.3 and 7.3: 0 wrong.
- The six comparisons on every pair of the 8.3 and 10.4 formats: 6,684,672, 0 wrong.
- binary32 and binary64 in round to nearest even beside the processor: `add`, `sub`, `mult`, `div`, `sqrt` and `fma`, 1,000,000 operand sets each in each format, 0 wrong. The operands sit at chosen exponent distances and on the edges of the significand.

Overflow is taken as IEEE 754 has it: infinity, except under truncation, where it is the largest finite number. A NaN is compared as a NaN whatever its payload.

## Running it

A C++17 compiler and Python 3. `AC_TYPES` is a checkout of [hlslibs/ac_types](https://github.com/hlslibs/ac_types).

```
export AC_TYPES=/path/to/ac_types
./run.sh repro                              # the three findings, a few lines each
./run.sh small "10.4" "add sub"             # every pair of the 10.4 format, four rounding modes
./run.sh small "6.3" "fma"                  # every triple of the 6.3 format
./run.sh small "10.4" "ceil floor trunc round"
./run.sh host                               # binary32 and binary64 beside the processor
./run.sh patched                            # the header with the patch: the reproducers and three of the runs again
```

A summary line reads `add   10.4  conv    1048576 operations,    3024 wrong {'one unit': 3024}`, with the first wrong cases above it.

| File | |
| --- | --- |
| [`actb.cpp`](actb.cpp) | every operand of a small format through one operation of the library, results as hex lines |
| [`acref.py`](acref.py) | the exact reference and the comparison |
| [`acfma.cpp`](acfma.cpp) | the `fma` case in binary32 and binary64 |
| [`acadd.cpp`](acadd.cpp) | 1.0 plus a far smaller number, eleven formats |
| [`aczero.cpp`](aczero.cpp) | `ceil`, `floor`, `trunc` and `round` beside the C library on operands whose result is zero |
| [`acbuiltin.cpp`](acbuiltin.cpp) | the same calls through `ac_ieee_float<binary32>`, built with and without `AC_IEEE_FLOAT_USE_BUILTIN` |
| [`achost.cpp`](achost.cpp) | binary32 and binary64 beside the processor's float and double |
| [`ac_std_float.patch`](ac_std_float.patch) | the seven lines |
