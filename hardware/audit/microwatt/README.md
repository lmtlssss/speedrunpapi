# Microwatt FPU

[`fpu.vhdl`](https://github.com/antonblanchard/microwatt/blob/f341bed306a9a7281bf65200df8cc1f0a002617d/fpu.vhdl) of [antonblanchard/microwatt](https://github.com/antonblanchard/microwatt), the OpenPOWER core, at commit `f341bed`. The unit also does the core's integer divisions.

It is driven at its own port: one `Execute1ToFPUType` record in, one `FPUToWritebackType` record out. The attributes the decoder would pass (single, signed, which operands are read) come from the core's own `decode1.vhdl`. A test is three instructions: `mtfsf` writes the rounding mode and the exception enables into the FPSCR, the instruction runs, `mffs` reads the FPSCR back.

The reference is [`ppcref.py`](ppcref.py): the Power ISA result worked out on fractions of integers and rounded once. It gives the value, the exception bits, FEX, FR, FI, FPRF, the compare field, and whether the target register is written at all.

## Enabled underflow: FPRF names a denormalized number

With `FPSCR[UE] = 1`, a result that is tiny before rounding is delivered rounded, with its exponent raised by 1536, or by 192 for the single forms and `frsp`, and "FPRF is set to indicate the class and sign of the result (± Normalized Number)" (Power ISA, Book I, Underflow Exception). When the rounding carries into the next power of two, the unit writes the right value and the right exception bits and sets FPRF to ± denormalized. The value in the register is a normal number.

```
fmul   FRA 1A88000000000000   FRC 2455555555555555          FPSCR before: rounding mode | UE

round to nearest     FRT 5EF0000000000000   FPSCR CA074020   FPRF 10100, + denormalized; 00100 is right
round toward +inf    FRT 5EF0000000000000   FPSCR CA074022   FPRF 10100
round toward zero    FRT 5EEFFFFFFFFFFFFF   FPSCR CA024021   FPRF 00100, right: this rounding does not carry
```

The operands are 3 x 2^-600 and (2^54 - 1)/3 x 2^-494. Their product is 2^54 - 1 times 2^-1094, fifty-four ones in a row, so rounding to nearest or upward gives 2^-1040, and 5EF0000000000000 is that with 1536 added to the exponent.

`fmuls` on `39FF000000000000` and `3CD0842100000000` (31 x 2^-100 and 1,082,401 x 2^-70, twenty-five ones) returns `42E0000000000000` with the same FPRF. `frsp` on `1F4FFFFFFFFFFFFF` does it too.

Cause. A rounding increment that carries goes through `ROUNDING_3`, which renormalizes and marks the result denormalized when its exponent is below the format's minimum (`v.denorm := exp_tiny`, line 2559). With underflow enabled the next state is `ROUND_UFLOW_EN`. It adds the bias to the exponent and leaves the mark, and FPRF is built from `r.r(UNIT_BIT) and not r.denorm` (line 3716). A tiny result that needs no increment, or whose increment does not carry, reaches `ROUND_UFLOW_EN` without passing `ROUNDING_3`, so it is classed correctly.

Fix: [`fpu-enabled-underflow-fprf.patch`](fpu-enabled-underflow-fprf.patch), one line. `ROUND_UFLOW_EN` clears the mark.

## `fcfidus`

Converting an unsigned 64-bit integer to single precision drops the bits under the single-precision round bit. This one is reported upstream by others, with its cause and fix, as [#476](https://github.com/antonblanchard/microwatt/issues/476): the decode sets the single-precision mask for `fcfid` and `fcfids` only. This harness ran into it in its first 8,600 tests. Two things it adds to that report:

- It starts at 2^26 + 1, not above 2^53. `fcfidus` of `0000000004000001` returns `4190000000000000` with XX and FI clear in every rounding mode, and the same value when rounding up, where `4190000020000000` is right. `0000000004000005` returns `4190000000000000` in round to nearest, where `4190000020000000` is right.
- Of 20,000 random 48-bit integers, 2,488 convert to the wrong value in round to nearest and 4,982 come back without XX: one in eight and one in four. Of 20,000 random 64-bit integers it is 76 and 185.

With the three lines of #476 added, the same 40,000 integers are right in all four rounding modes.

## What agrees

With both changes in place:

- 155,400 tests with the exception enables set: 37 instructions (`fadd` to `fnmsub` and their single forms, `frsp`, the eight `fcti*`, the four `fcfid*`, the four `fri*`, `fcmpu`, `fcmpo`), 600 operand sets each, under seven settings of the enables: none, XE, ZE, UE, OE, VE, all five. Value, exception bits, FEX, FR, FI, FPRF and the compare field are right, the target is left alone for every enabled invalid operation and zero divide, and no interrupt is raised with `MSR[FE0 FE1] = 00`. Operands sit at both ends of the exponent range, around the enabled-exception bias, on long runs of ones, and include zeros, infinities and both kinds of NaN.
- 344,000 more tests with every exception disabled, on the operand generators the other audits in this directory use: 43 instructions, 2,000 operand sets each, four rounding modes. Those generators are not in this folder.

Without the one-line fix, 55 of the 155,400 differ, all in FPRF as above and all with UE set: 48 in `frsp`, 5 in `fmul`, one in `fmadd` and one in `fnmadds`.

The integer divisions and remainders (`divd`, `divdu`, `divw`, `divwu`, `divde`, `divdeu`, `divwe`, `divweu`, `modsd`, `modud`, `modsw`, `moduw`) are compared with integer arithmetic by [`mw_idiv.py`](mw_idiv.py), with OE and Rc both ways: quotient or remainder, OV, OV32, SO, CR0. What the ISA leaves undefined is not compared: the result when the divisor is zero or the quotient does not fit, and the upper half of the word forms.

## Running it

GHDL and Python 3. `MICROWATT` is a checkout of the core.

```
export MICROWATT=/path/to/microwatt
./run.sh build                                   # tb_mw, with the core's fpu.vhdl
./run.sh one t1 tb_mw fmul all 20 1A88000000000000::2455555555555555

cp $MICROWATT/fpu.vhdl fpu_fixed.vhdl
patch fpu_fixed.vhdl < fpu-enabled-underflow-fprf.patch
./run.sh build $PWD/fpu_fixed.vhdl tb_fix
./run.sh one t2 tb_fix fmul all 20 1A88000000000000::2455555555555555

./run.sh enabled 2 600 en2 tb_fix                # the 155,400 tests
./run.sh idiv 2 50000 idiv2 tb_fix               # 600,000 divisions and remainders
```

`one` takes the instruction, the rounding mode (0 to 3, or `all`), the enable bits in hex as they sit in the FPSCR (VE 80, OE 40, UE 20, ZE 10, XE 08) and operands as `FRA:FRB:FRC` in hex. A report line shows what the unit returned and what is exact.

| File | |
| --- | --- |
| [`tb_mw.vhd`](tb_mw.vhd) | the testbench: one instruction per line of a vector file, one result line each |
| [`ppcref.py`](ppcref.py) | the reference |
| [`mwinsn.py`](mwinsn.py) | instruction words, and the decode attributes read from `decode1.vhdl` |
| [`mw_enabled.py`](mw_enabled.py) | vectors and the comparison for the floating-point instructions |
| [`mw_idiv.py`](mw_idiv.py) | the same for the integer divisions |
| [`mkrand.py`](mkrand.py) | random integers of a given width, for `fcfidus` |
