# `ac_math::ac_div`

[`ac_div.h`](https://github.com/hlslibs/ac_math/blob/4bc5da6682e5ecbb9ff41ffe5f04725f3bdedc30/include/ac_math/ac_div.h) of [hlslibs/ac_math](https://github.com/hlslibs/ac_math), the math library that goes with the Algorithmic C datatypes Siemens publishes for high-level synthesis, at commit `4bc5da6` (Release Build 2026.3.1). `ac_div` divides integers, fixed-point numbers, floats and complex numbers and rounds the quotient into the output type by that type's quantization mode. `ac_sqrt` was run the same way and is right.

Each configuration is one instantiation: the operand widths, the output width, one of the eight quantization modes and one of two overflow modes. Every operand value of a configuration goes through the function, and every result is compared with [`acm.py`](acm.py): the operation on fractions of integers, quantized once. The definitions of the quantization and overflow modes in `acm.py` are checked against the library's own `ac_fixed` assignment first ([`qtest.cpp`](qtest.cpp), [`acq.py`](acq.py)): 4,096 assignments, 0 differ.

5,802 configurations: 4,480 fixed-point divisions, half unsigned and half signed, 1,296 fixed-point square roots, 10 integer divisions and 16 integer square roots.

## Fixed-point division does not write its result when the quotient is below the output's last place

When the largest possible quotient is smaller than the last place of the output type, the unsigned `ac_div` returns early. It sets a local variable to zero and returns without assigning the output.

```cpp
if (ZI-1 < -QF) {
  // MSB of result is smaller than LSB of requested output
  quotient_temp = ac_fixed<QW,QI,false,QQ,QO>(0);
  return !! dividend;                                  // line 325: `quotient` is never written
}
```

```cpp
ac_fixed<8, 0, false> n = 0.5;
ac_fixed<8, 8, false> d = 3;
ac_fixed<8, 8, false> q = 77;        // what the variable held before
ac_math::ac_div(n, d, q);            // q is still 77; 0 is right
```

The signed `ac_div` calls the unsigned one with a temporary that it never sets, and builds its result from it. What comes back depends on the compiler and its options:

```
ac_fixed<8,0,true> n = -0.5;  ac_fixed<8,8,true> d = 3;  ac_fixed<8,8,true> q;      floor(-0.5 / 3) = -1

clang -O0                                        -2
clang -O2                                         0
clang -O1 -ftrivial-auto-var-init=pattern        85
clang -O1 -ftrivial-auto-var-init=zero           -1
```

The sweep runs every call twice, with the output variable holding `0101...` and then `1010...` beforehand, and is built with `-ftrivial-auto-var-init=pattern` so that an unset variable is not zero by luck:

| | calls | wrong | configurations |
| --- | --- | --- | --- |
| unsigned fixed-point division | 315,392 | 7,648, each one the earlier content of the output | 128 of 2,240 |
| signed fixed-point division | 312,256 | 3,840 | 72 of 2,184 that compile |

All eight quantization modes are affected. A first sweep, built without that option and with the outputs left unset, reported 336 wrong values: unset memory is mostly zero in such a build, and zero is the right answer on this path.

## Signed fixed-point division with a saturating output

With an output whose overflow mode is not `AC_WRAP`, the signed `ac_div` sizes its temporary quotient by the magnitude bound alone (line 397):

```cpp
const int ZI = (QO == AC_WRAP) ? QI : NI+(DW-DI);
const int ZW = ZI+(QW-QI);
```

When the output's last place is at or above that bound, `ZW` is zero or negative. Of the 1,120 signed configurations with `AC_SAT`:

- 56 do not compile (`ac_fixed` with a width of zero or less, `ac_div.h` lines 418 and 436 and `ac_fixed.h` line 409). Example: `ac_fixed<3,-1,true>` divided by `ac_fixed<3,3,true>` into `ac_fixed<4,4,true,AC_TRN,AC_SAT>`.
- 4 stop at the library's assertion "Attempting to read bit beyond MSB" on 172 calls (`AC_TRN`, a zero-width temporary indexed at `[0]`).
- 8 return 0 on an exact tie that rounds away from zero: 16 calls, `AC_RND_INF` and `AC_RND_CONV_ODD`. Example: -2 / 2 into `ac_fixed<5,6,true,AC_RND_INF,AC_SAT>`, whose last place is 2. The quotient -1 is a tie between 0 and -2, and -2 is right.

These are what is left when the first defect is fixed alone.

Both are reported, on 13 November 2026, as [hlslibs/ac_math#11](https://github.com/hlslibs/ac_math/issues/11).

## The returned flag of signed integer division

`ac_div` returns true when the remainder is nonzero. The unsigned integer version tests its full internal remainder. The signed one tests the remainder after it has been cut to the width of the remainder output, so with a remainder output narrower than the divisor it returns false for a nonzero remainder: 14 calls of `ac_int<4,true>` divided by `ac_int<4,true>` with a 2-bit remainder, for example 4 / 5.

## The patch

[`ac_div.patch`](ac_div.patch), two lines: the early return assigns the output, and the signed temporary gets integer bits for one unit of the output's last place as well as for the magnitude bound.

```cpp
quotient = quotient_temp;
const int ZI = (QO == AC_WRAP) ? QI : AC_MAX(NI+(DW-DI), QI-QW+1);
```

With it all 5,802 configurations compile and 689,808 calls are right in both runs: no wrong value, no assertion, no result that depends on the earlier content of the output. The 14 flags of the signed integer division are not changed by it.

## What agrees

On the header as published: `ac_sqrt` on unsigned fixed-point types in all eight quantization modes (54,144 calls over 1,296 configurations) and on integers (2,592 calls); integer `ac_div`, quotient and remainder, unsigned and signed (2,288 calls); and the fixed-point divisions outside the two cases above.

`ac_shift_left` and `ac_shift_right` of [`ac_shift.h`](https://github.com/hlslibs/ac_math/blob/4bc5da6682e5ecbb9ff41ffe5f04725f3bdedc30/include/ac_math/ac_shift.h), which the rest of the library is built on, were run the same way by [`acs.py`](acs.py): both directions, signed and unsigned operands, an `int` and an `unsigned int` count, five operand types, six output types, the eight quantization modes, wrapping and saturating outputs. That is 3,840 configurations, every operand shifted by every count from -10 to 10: 786,432 calls, 0 wrong, and nothing that depends on the earlier content of the output.

## Running it

A C++17 compiler and Python 3. `AC_TYPES` and `AC_MATH` are checkouts of [hlslibs/ac_types](https://github.com/hlslibs/ac_types) and [hlslibs/ac_math](https://github.com/hlslibs/ac_math).

```
export AC_TYPES=/path/to/ac_types AC_MATH=/path/to/ac_math
c++ -std=c++17 -w -I $AC_TYPES/include -I $AC_MATH/include acdiv.cpp -o acdiv && ./acdiv

c++ -std=c++17 -w -I $AC_TYPES/include qtest.cpp -o qtest && ./qtest | python3 acq.py

CXXEXTRA=-ftrivial-auto-var-init=pattern python3 run.py out 8          # the sweep, about two minutes

mkdir -p patched/ac_math && cp $AC_MATH/include/ac_math/ac_div.h patched/ac_math/
patch -p2 -d patched < ac_div.patch
CXXEXTRA=-ftrivial-auto-var-init=pattern python3 run.py out_patched 8 $PWD/patched

ACM_MODULE=acs CXXEXTRA=-ftrivial-auto-var-init=pattern python3 run.py out_shift 8      # the shifts
```

`run.py` writes the test programs, compiles them, sets aside the configurations the library does not compile for (with the compiler's error for each in `nocompile_why.json`), runs the rest twice and compares. The library's assertions are caught through its own `AC_USER_DEFINED_ASSERT` hook; with that hook defined `ac_fixed.h` needs `<iostream>` included before it.

| File | |
| --- | --- |
| [`acm.py`](acm.py) | the configurations, the generated test programs, the exact reference and the comparison |
| [`acs.py`](acs.py) | the same for `ac_shift_left` and `ac_shift_right` |
| [`run.py`](run.py) | build, run twice, compare |
| [`acdiv.cpp`](acdiv.cpp) | three plain cases |
| [`qtest.cpp`](qtest.cpp), [`acq.py`](acq.py) | the reference's quantization and overflow against the library's own `ac_fixed` |
| [`flags.py`](flags.py) | the calls whose returned flag is not "the remainder is nonzero" |
| [`ac_div.patch`](ac_div.patch) | the two lines |
