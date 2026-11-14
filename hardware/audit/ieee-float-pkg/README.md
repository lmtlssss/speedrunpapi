# IEEE 1076 float package

`ieee.float_pkg` is the floating-point package of the VHDL standard, IEEE Std 1076-2008 and 1076-2019. The source is the IEEE's own: [`ieee/float_generic_pkg-body.vhdl`](https://opensource.ieee.org/vasg/Packages/-/blob/release/ieee/float_generic_pkg-body.vhdl) on the `release` branch of `opensource.ieee.org/vasg/Packages`, 5,712 lines, `$Revision: 1220 $`. The working group's `develop` branch at `gitlab.com/IEEE-P1076/Packages` has the same bytes, and GHDL and NVC ship them unchanged. The runs here are in GHDL 7.0.0-dev and NVC 1.23.1, and where both ran the same vectors they wrote the same result file.

The package is set beside exact arithmetic. An operand is a sign and a fraction of two integers, the operation is done on the fractions, and the result is rounded once into the format in the rounding style the call names. [`exact.py`](exact.py) is that reference.

## Plain calls

With the package's own settings: `round_nearest`, 3 guard bits, denormal numbers on.

```
call                                        returns                   exactly rounded
sqrt (2.0) in float64                       3FF6A09E667F3BCC          3FF6A09E667F3BCD
sqrt (14.0)                                 406F7750                  406F7751
sqrt (2.0**-149)                            4.2e-22                   3.7e-23
mac (-6.0, -1.0, -5.0)                      -15.0                     1.0
mac (-5.0, 1.0, 4.0)                        15.0                      -1.0
mac (1.0, 1.0, -infinity)                   +infinity                 -infinity
mac (1 + 2.0**-23, 1 - 2.0**-23, -1.0)      -2.0**-26                 -2.0**-46
resize (2.0**-512 in float64, 8, 23)        1.0                       0.0
resize (2.0**600 in float64, 8, 23)         2.0**88                   +infinity
resize (2.0**-1074 in float64, 8, 23)       +infinity                 0.0
resize (2.0**-650 in float64, 8, 23)        stops the simulator       0.0
reciprocal (2.0**127)                       +infinity                 2.0**-127
divide (2.0**-149, 2.0)                     2.0**-149                 0.0
dividebyp2 (3 * 2.0**-149, 2.0)             2.0**-149                 2.0**-148
scalb (1.0, 300)                            0.0                       +infinity
scalb (+infinity, -10)                      2.0**118                  +infinity
to_signed (0.50000006, 32)                  0                         1
to_unsigned (199.78125, 8)                  199                       200
```

And where the call names a rounding style:

```
divide (6.0, 3.0, round_inf)                2.0000002                 2.0
reciprocal (2.0, round_inf)                 0.50000006                0.5
add (largest, largest, round_zero)          +infinity                 largest
multiply (2.0**-100, 2.0**-100, round_inf)  0.0                       2.0**-149
add (1.0, -1.0, round_neginf)               +0.0                      -0.0
to_signed (2.25, 8, round_inf)              2                         3
to_float (100000, 5, 10, round_zero)        +infinity                 65504.0, the largest
```

[`plain.vhd`](plain.vhd) makes these calls and prints `WRONG` beside each result that is not the exactly rounded one: 24 lines, and the 25th call stops the simulator with an index out of bounds at line 358 of the package body.

The plain operands are not rare ones. Of the integers 1 to 4,096, `sqrt` returns a float32 one unit off for 256 and a float64 one unit off for 264. Of the 4,913 triples made from -6 to 6, 0.25, 0.5, 1.5 and 10, `mac` returns the wrong float32 for 290. `resize` from float64 to float32 returns +infinity for every power of two from 2^-1074 to 2^-1024, stops the simulator from 2^-662 to 2^-639, returns 2^(e+512) from 2^-638 to 2^-512 and 2^(e-512) from 2^513 to 2^639.

## Counts

10,000 calls per operation, format and rounding style, on operands aimed at the places arithmetic breaks: denormal operands and results, both ends of the exponent range, fractions that round up into the next binade, exact ties, signed zeros, infinities. A cell is the number of results that are not the exactly rounded one, of the calls compared. A conversion whose result does not fit the integer is not compared.

```
float32                            round_nearest      round_zero         round_neginf       round_inf
add                                0 of 10,000        304 of 10,000      312 of 10,000      159 of 10,000
subtract                           0 of 10,000        314 of 10,000      312 of 10,000      143 of 10,000
multiply                           0 of 10,000        1,102 of 10,000    781 of 10,000      775 of 10,000
divide                             27 of 10,000       670 of 10,000      2,324 of 10,000    2,395 of 10,000
sqrt                               735 of 10,000      581 of 10,000      542 of 10,000      774 of 10,000
mac                                2,671 of 10,000    3,697 of 10,000    3,213 of 10,000    3,302 of 10,000
reciprocal                         384 of 10,000      586 of 10,000      1,093 of 10,000    2,613 of 10,000
resize to a narrower format        422 of 20,000      2,728 of 20,000    2,516 of 20,000    2,466 of 20,000   272 more stop the simulator
resize to a wider format           0 of 20,000        0 of 20,000        0 of 20,000        0 of 20,000
to_float (signed, 32 and 64 bits)  0 of 20,000        0 of 20,000        0 of 20,000        0 of 20,000
to_signed (8, 32, 64 bits)         613 of 28,637      0 of 28,626        5,934 of 28,608    5,898 of 28,623
to_unsigned (8, 32, 64 bits)       280 of 16,506      0 of 17,133        0 of 14,493        5,964 of 17,145
to_integer                         0 of 10,000        0 of 10,000        1,921 of 10,000    1,973 of 10,000
to_float (integer)                 0 of 10,000        0 of 10,000        0 of 10,000        0 of 10,000
dividebyp2                         1,542 of 10,000    1,904 of 10,000    2,313 of 10,000    2,262 of 10,000
scalb                              2,653 of 10,000    3,088 of 10,000    3,381 of 10,000    3,401 of 10,000
```

```
float64                            round_nearest      round_zero         round_neginf       round_inf
add                                0 of 10,000        260 of 10,000      311 of 10,000      138 of 10,000
subtract                           0 of 10,000        283 of 10,000      317 of 10,000      147 of 10,000
multiply                           0 of 10,000        1,163 of 10,000    852 of 10,000      866 of 10,000
divide                             18 of 10,000       698 of 10,000      2,495 of 10,000    2,406 of 10,000
sqrt                               1,278 of 10,000    619 of 10,000      659 of 10,000      799 of 10,000
mac                                2,673 of 10,000    3,697 of 10,000    3,285 of 10,000    3,290 of 10,000
reciprocal                         350 of 10,000      477 of 10,000      1,087 of 10,000    2,623 of 10,000
resize to a narrower format        801 of 30,000      4,116 of 30,000    3,980 of 30,000    4,014 of 30,000   445 more stop the simulator
resize to a wider format           0 of 10,000        0 of 10,000        0 of 10,000        0 of 10,000
to_float (signed, 32 and 64 bits)  0 of 20,000        0 of 20,000        0 of 20,000        0 of 20,000
to_signed (8, 32, 64 bits)         618 of 28,219      0 of 28,231        6,161 of 28,340    5,952 of 28,262
to_unsigned (8, 32, 64 bits)       321 of 16,330      0 of 16,839        0 of 14,237        6,155 of 16,776
to_integer                         0 of 10,000        0 of 10,000        2,125 of 10,000    2,183 of 10,000
to_float (integer)                 0 of 10,000        0 of 10,000        0 of 10,000        0 of 10,000
dividebyp2                         1,543 of 10,000    1,902 of 10,000    2,321 of 10,000    2,391 of 10,000
scalb                              2,218 of 10,000    2,540 of 10,000    2,982 of 10,000    2,967 of 10,000
```

In float32 that is 81,068 wrong and 272 stops in 859,771 calls, and in float64 86,081 wrong and 445 stops in 857,234. The same calls in float16 give 113,980 wrong in 866,782, and in float128 90,744 wrong and 585 stops in 855,777.

Where a format is small enough, every operand there is:

```
format                                      calls                                             compared       wrong
7 bits, 3 of exponent and 3 of fraction     every operand, every pair, every triple of mac    8,692,326      1,271,619
10 bits, 4 of exponent and 5 of fraction    every operand and every pair                      17,340,682     883,716
float16                                     every operand of the one-operand functions        2,998,266      266,342
```

`mac` in `round_nearest` is wrong for 243,520 of the 2,097,152 triples of the 7-bit format.

## Causes

Line numbers are those of the IEEE file.

**`normalize`, line 422.** Every result goes through `exp := resize (expon, exp'length) + shiftr`. The exponent comes in at the width of the caller's format and is cut to two bits more than the target's. From float64 to float32 that is ten bits, so the exponent is taken modulo 1,024: 2^-512 comes out as 1.0 and 2^600 as 2^88. Where the cut exponent lands among the denormal numbers, the shift count that follows indexes outside the fraction and the simulator stops. In the same function a result too large for the format is infinity in every rounding style and a result too small is zero in every rounding style. Rounding toward zero gives the largest number, and rounding away from zero gives the smallest.

**`divide`, line 1243, and `reciprocal`, line 1099.** The sticky bit handed to the rounding is the constant `'1'`. An exact quotient is rounded as if something were left over: one unit up in `round_inf`, and to the wrong side of an exact tie in `round_nearest`, which happens among denormal quotients.

**`reciprocal`, lines 1053 to 1093.** The exponent of the result, -e - 3, is kept in as many bits as e, and for the top binade it does not fit. In float32 every argument from 2^127 up returns infinity, and in float64 every argument from 2^1023 up. 1/-0 returns +infinity and 1/-infinity returns +0.

**`sqrt`, line 1787.** Newton's iteration from (1 + x)/2, `fraction_width/4 + 1` steps in truncated fixed point, and the result goes to the rounding without a sticky bit. For a normal argument it ends on the root or one unit beside it: in the vectors above it is one unit off for 607 of 9,156 normal float32 arguments and 1,146 of 9,236 normal float64 ones, and never further. For a denormal argument the start is too far away for that many steps: 128 of 359 float32 denormals are wrong, 104 of them by more than two units, and `sqrt (2.0**-149)` returns 11 times the root.

**`mac`, lines 1438 to 1536.** The product is cut to the width of one operand before `c` is added (lines 1529 and 1536), so a sum that cancels returns what the cut left. Where the product and `c` have the same exponent and unlike signs and the product is the larger, line 1514 subtracts the larger from the smaller: (-6)(-1) + (-5) returns -15. An infinite `c` takes the sign of the product, and infinity minus infinity returns infinity (line 1438).

**`add`, line 839.** An exact zero from operands of unlike signs is +0 in every style. The paragraph the comment cites, IEEE 854 6.3, makes it -0 when rounding toward minus infinity.

**`to_signed`, `to_unsigned`, lines 301 to 345, and `to_integer`, line 3193.** Three bits below the integer are kept and the rest are dropped without a sticky bit, so 0.50000006 is taken for one half and goes to the even neighbour, 0. For a number that fills every bit of a `to_unsigned` result the three bits are zeros: 199.78125 into 8 bits returns 199. `round_inf` and `round_neginf` look at the half bit only, so 2.25 rounded up is 2.

**`resize`, line 2407.** -0 to a narrower format returns +0, and the comment says `hate -0`. To a wider format it stays -0.

**`to_float` of an integer, lines 2676 and 2803.** A number too large for the format returns infinity in every rounding style.

**`dividebyp2`, line 1378, and `Scalb`, lines 4601 to 4610.** Both hand the result to `normalize` with no guard bits, so a denormal result is cut off where it should be rounded. `Scalb` adds N in `exponent_width + 1` bits, where a large N wraps, and it scales infinity like a number. `dividebyp2` takes a denormal power of two for a divisor that is not a power of two.

**With `denormalize` false.** A zero is broken up with a higher exponent than a number of the lowest binade, so `add` of a zero and such a number of the opposite sign subtracts the number from zero and returns the wrapped difference. `reciprocal` treats those numbers as the denormals they are not.

## The patch

[`float_generic_pkg-body.patch`](float_generic_pkg-body.patch) applies to the IEEE file. It changes the package body only, 33 hunks, and no declaration.

- `normalize` decides between zero, denormal, normal and infinity on the exponent at its full width, and returns the largest or the smallest number where the rounding style asks for it.
- `divide` and `reciprocal` take the sticky bit from the remainder of the division. `reciprocal` keeps its exponent two bits wider and gives zero and infinity the sign of the argument.
- `sqrt` takes the integer square root of the significand one bit per step, with the remainder as the sticky bit.
- `mac` places the whole product and `c` in one window of 3 * `fraction_width` + 9 bits, adds or subtracts there and rounds once. It is a fused multiply-add.
- The conversions to integers keep three bits of the number whatever the shift, collect the rest in a sticky bit, and round up in the directed styles on any bit below the integer.
- `add` returns the other operand when one is zero and gives an exact zero the sign the rounding style calls for. `resize` keeps the sign of zero.
- `to_float` of an integer returns the largest number where the style rounds toward zero.
- `dividebyp2` and `Scalb` round a denormal result with guard bits. `Scalb` returns infinity and zero as they are and takes any N.

On the same vectors:

```
                                                          the package as shipped       patched
four formats, 10,000 per cell, 3,439,564 calls            371,873 wrong, 1,302 stop 0 wrong, 0 stop
the 7-bit format, 8,692,326 calls                         1,271,619 wrong              0
the 10-bit format, 17,340,682 calls                       883,716 wrong                0
float16, the one-operand functions, 2,998,266 calls       266,342 wrong                0
plain.vhd, 25 calls                                       24 wrong, 1 stop             0
```

GHDL and NVC wrote the same result files with either package: 8,693,248 lines for the 7-bit format and 3,680,000 for the four formats, the 1,302 stops on the same lines. The reference itself was set beside this machine's own arithmetic on the float32 and float64 vectors of add, subtract, multiply, divide and sqrt in `round_nearest`: 99,135 operations, none different.

The package takes its guard bits and its denormal numbers as parameters. On 1,000 calls per cell in float16, float32 and float64:

```
setting                        calls       patched right, shipped wrong     neither right     shipped right, patched wrong
3 guard bits, the default      258,075     28,103                           0                 0
4 guard bits                   258,075     27,758                           0                 0
2 guard bits                   258,075     28,760                           112               0
1 guard bit                    258,075     30,212                           2,194             0
denormalize false              255,606     27,745                           0                 0
```

With two guard bits 112 results of `add` and `subtract` are not the rounded ones, and with one guard bit 2,194 of `add`, `subtract` and `multiply`: too few bits to round every result, and both packages return the same bits on those lines. With no guard bits nothing is rounded: the patched `sqrt`, `mac` and `reciprocal` then return the exact result cut off toward zero on every line, where the shipped ones do on 10,207 of 11,141, 3,902 of 9,750 and 10,749 of 11,102. With `denormalize` false the comparison is with that setting's own numbers, where an exponent field of zero is one more binade of numbers with a leading one.

## Running it

GHDL or NVC, Python 3.9 or later, and the three files `float_generic_pkg.vhdl`, `float_generic_pkg-body.vhdl` and `float_pkg.vhdl` from the directory `ieee` of the IEEE repository or from `lib/ghdl/src/ieee2008` of a GHDL installation.

```
sh run.sh ghdl /path/to/ieee 100      # plain.vhd, then 100 vectors per operation, format and style: half a minute
sh run.sh nvc  /path/to/ieee 10000    # the tables above
```

With 100 the last lines read `3696 wrong and 8 stops in 34440 operations` for the package as shipped and `0 wrong and 0 stops in 34440 operations` for the patched one, in both simulators. NVC is the faster of the two on the large runs: the shipped `sqrt` and `divide` work in fixed point and are slow in float128.

`run.sh` compiles the patched body into a library of its own, `patched`, beside the declaration it belongs to, and runs each testbench twice: against the package the simulator ships and against that library. [`tb_float_pkg.vhd`](tb_float_pkg.vhd) reads one operation per line and writes the result; `exact.py run` restarts it behind a line that stops the simulator.

```
python3 exact.py gen 2026 10000 5,10 8,23 11,52 15,112 > vectors.txt     # the vectors of the tables above
python3 exact.py all 3,3 > vectors.txt                                   # every operand of the 7-bit format
python3 exact.py check vectors.txt results.txt
```

To use the patched package in a design, compile `float_generic_pkg.vhdl` and the patched body into a library and instantiate `float_pkg` from it, as `run.sh` does.

## Not covered

`remainder`, `modulo`, `Logb`, `Nextafter`, the comparisons, the conversions with `real` and with fixed point, the text input and output, operands of two different formats in one call, and `check_error` false.

The VHDL-93 version of the package, `float_pkg_c.vhdl` in [FPHDL/fphdl](https://github.com/FPHDL/fphdl), carries the same lines. It was not run here.

## Reported

To the IEEE P1076 working group on 13 November 2026 as [VHDL-Issues#388](https://gitlab.com/IEEE-P1076/VHDL-Issues/-/work_items/388) and by mail, and as [ghdl/ghdl#3486](https://github.com/ghdl/ghdl/issues/3486), [nickg/nvc#1758](https://github.com/nickg/nvc/issues/1758) and [FPHDL/fphdl#4](https://github.com/FPHDL/fphdl/issues/4).
