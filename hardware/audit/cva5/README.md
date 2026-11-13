# CVA5

[openhwgroup/cva5](https://github.com/openhwgroup/cva5), `master` at `2acf79f`, the floating-point unit `fp_unit` driven at its issue and writeback interfaces.

## Division and square root issued back to back

A division or square root whose result is a zero, an infinity or a NaN never completes when it is issued in the cycle the previous one is acknowledged. Upstream issue [#34](https://github.com/openhwfoundation/cva5/issues/34).

```
first request        second request, issued in the first cycle the unit is ready      master
fdiv.d  3.0 / 2.0    fdiv.d  0.0 / 2.0                                                1.5, then no answer
fsqrt.d 2.0          fsqrt.d +0.0                                                     1.4142135623730951, then no answer
fdiv.s  1.0 / 3.0    fdiv.s  1.0 / 0.0                                                0.33333334, then no answer
```

`fp_div.sv` and `fp_sqrt.sv` accept a request in the acknowledge cycle, `issue.ready = ~busy | wb.ack`, and the register `early_exit` is cleared by `wb.ack` before it can be set for the new request. A special case does not start the iterative core, so nothing raises `wb.done` again.

In `fp_div.sv` the special result is also selected for one cycle only, by `new_request_r`. When the acknowledge comes a cycle later, because a square root finishes in that cycle, the outputs show what the divider core kept from the previous division.

```
after fdiv.d 3.0 / 2.0 and an fsqrt.d that finishes in the cycle of the early result

fdiv.d  NaN / 1.0    expected NaN, no flags    master +inf, OF|NX
fdiv.d  1.0 / 0.0    expected +inf, DZ         master +inf, DZ|OF|NX
fdiv.d  0.0 / 2.0    expected 0, no flags      master 0, UF|NX
```

[`div_sqrt_early_exit.patch`](div_sqrt_early_exit.patch) tests the new request first and holds the special result until it is acknowledged.

```
1,000,000 requests per unit, issued back to back      master, no answer      patched
fdiv.s                                                67,439                 0
fdiv.d                                                37,932                 0
fsqrt.s                                               54,971                 0
fsqrt.d                                               39,437                 0
```

## Square root in double precision

Some inexact square roots are returned as exact. Upstream issue [#35](https://github.com/openhwfoundation/cva5/issues/35).

```
fsqrt.d 0x400ffffff6000001        the root lies 0.11 ulp above 0x3ffffffffb000000

mode   expected                    master
RNE    0x3ffffffffb000000  NX      0x3ffffffffb000000  no flags
RTZ    0x3ffffffffb000000  NX      0x3ffffffffb000000  no flags
RDN    0x3ffffffffb000000  NX      0x3ffffffffb000000  no flags
RUP    0x3ffffffffb000001  NX      0x3ffffffffb000000  no flags
RMM    0x3ffffffffb000000  NX      0x3ffffffffb000000  no flags
```

It needs a root that is a 29-bit number plus less than 2^-55 of it. The operand above has the significand (s·s + 7) / 32 with s = 2^29 - 5.
Uniformly random operands do not show it: 0 of 1,000,000. In a set of 1,000,000 operands built around that form, 556,146 return without NX on `master` and 0 with the patch. Single precision is right on 5,000,000.

In `fp_sqrt_core.sv` the partial remainder can be twice the partial root and is shifted left by two bits before each subtraction. The working registers have the width of the result, and only bits `[DATA_WIDTH-3:0]` of the remainder and of the partial root go into the next step. The last steps need the two bits that are dropped.

[`sqrt_core_model.py`](sqrt_core_model.py) is a bit-true model of the core beside the integer square root. With the registers as written, the last bit of the 57-bit result is wrong for 59,692 of 100,000 uniformly random operands, and the remainder that feeds the sticky bit is wrong with it. Rounding sees the error only when every bit under the guard bit is zero.

```
python3 sqrt_core_model.py 400ffffff6000001
400ffffff6000001 as written: result 1ffffffb0000000 remainder_zero=True | widened: result 1ffffffb0000001 remainder_zero=False | exact: 1ffffffb0000001 remainder_zero=False
```

[`sqrt_core_width.patch`](sqrt_core_width.patch) gives the working registers two more bits and takes the sticky from the remainder of the last step.

## Single-precision operations on registers that are not NaN-boxed

A single-precision operation reads such a register as the canonical NaN. Upstream issue [#36](https://github.com/openhwfoundation/cva5/issues/36).

```
fmul.s    rs1 = rs2 = 0x0000000000000000     expected 0x7fc00000, no flags     master 0x7fc00000 with NX; round-up 0x7fc00001
fclass.s  rs1 = 0x0000000000000000           expected 0x200                    master 0x220
fclass.s  rs1 = 0x3ff0000000000000           expected 0x200                    master 0x220
```

`fp_rs_preprocess.sv` takes the hidden bit of a single from the low word even when the register is not boxed, and `fp_wb2int_misc.sv` excludes only zero from the two subnormal classes.
[`nan_boxing.patch`](nan_boxing.patch) changes the three lines.

## The rest of the unit

Addition, subtraction, fused multiply-add, double-precision multiplication, division and single-precision square root issued one at a time, the conversions between formats and to and from integers, comparisons, minimum and maximum, sign injection and the moves: 5,000,000 operands per operation and precision over five rounding modes, 0 wrong values and 0 wrong flags.
With the three patches, every stream above and five mixed streams of 3,200,000 requests issued back to back return no wrong value, no wrong flag and no missing answer.
