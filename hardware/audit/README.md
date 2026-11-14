# Arithmetic audits of open cores

Each core is simulated beside exact arithmetic on vectors aimed at the places arithmetic breaks: subnormal operands and results,
both exponent limits, significands that round up into the next binade, exact ties, signed zeros, infinities.
Reference: IEEE 754 round to nearest even from the host, and integer arithmetic for the other rounding modes.
Every row below has a reproducer that fits on one line.

## Results

| Core | Unit | Vectors | Wrong | Upstream |
| --- | --- | --- | --- | --- |
| [dawsonjon/fpu](https://github.com/dawsonjon/fpu) | `double_divider` | 20,000 | 1 mixed; 20,000 of 20,000 aimed | [#31](https://github.com/dawsonjon/fpu/pull/31) |
| dawsonjon/fpu | `double_to_float` | 50,000 | 450 | [#32](https://github.com/dawsonjon/fpu/pull/32) |
| dawsonjon/fpu | `divider`, `multiplier`, `double_multiplier`, `adder`, `double_adder` | 20,000 each | 0 | |
| dawsonjon/fpu | `float_to_double`, `long_to_double`, `int_to_float`, `double_to_long`, `float_to_int` | 50,000 each | 0 | |
| OpenCores `double_fpu` | add, sub | 20,000 each | 905, 905 | no maintained upstream |
| OpenCores `double_fpu` | mul | 20,000 | 120 | |
| OpenCores `double_fpu` | div | 20,000 | 903 | |
| OpenCores `fpu` (single) | add, sub, mul, div | 80,000 | 7 | no maintained upstream |
| [openrisc/or1200](https://github.com/openrisc/or1200) | `or1200_fpu_arith` | 80,000 | 152 | |
| [openrisc/mor1kx](https://github.com/openrisc/mor1kx) | `pfpu32`: add, sub, mul, div, four rounding modes | 8,000,000 each | 124,892, 125,288, 177,982, 259,566; none in round to nearest | [#181](https://github.com/openrisc/mor1kx/issues/181) |
| openrisc/mor1kx | `pfpu32`: int to float, float to int, 13 compares | 8,000,000 each; 1,000,000 compares | 0 | |
| [openrisc/or1k_marocchino](https://github.com/openrisc/or1k_marocchino) | `pfpu_marocchino`: add, sub, mul, div, single and double, four rounding modes | 8,000,000 each | single as mor1kx; double 129,338, 128,898, 176,716, 255,254 | [#30](https://github.com/openrisc/or1k_marocchino/issues/30) |
| openrisc/or1k_marocchino | `pfpu_marocchino`: all operations interleaved | 15,680,000 | 56,402 after a division by zero | [#29](https://github.com/openrisc/or1k_marocchino/issues/29) |
| [bespoke-silicon-group/basejump_stl](https://github.com/bespoke-silicon-group/basejump_stl) | `bsg_fpu_add_sub`: add, sub, single and double | 2,080,000 each | 68,280, 68,308; 66,020, 65,835 | [#765](https://github.com/bespoke-silicon-group/basejump_stl/pull/765) |
| bespoke-silicon-group/basejump_stl | `bsg_fpu_mul`, `bsg_fpu_f2i`, single and double | 3,120,000; 2,080,000 | 0 values; overflow and invalid flags in three cases | offered in #765 |
| bespoke-silicon-group/basejump_stl | `bsg_fpu_i2f`, `bsg_fpu_cmp`, `bsg_fpu_classify`, sticky, leading zeros | 2,080,000 each | 0 | |
| [black-parrot/black-parrot](https://github.com/black-parrot/black-parrot) | decoder, reservation stage and the aux, fma and long pipes: 29 F and D operations, single and double, five rounding modes | 6,960,000 | 907, all `fcvt.s.l` and `fcvt.s.lu` to nearest | [#1380](https://github.com/black-parrot/black-parrot/pull/1380) |
| black-parrot/black-parrot | `fcvt.s.l`, `fcvt.s.lu` to nearest, integers aimed at halfway points | 399,621 | 37,541 | #1380 |
| black-parrot/black-parrot | RV64M multiply, divide and remainder through the same pipes | 1,300,000 | 0 | |
| [lowRISC/muntjac](https://github.com/lowRISC/muntjac) | FPU: add, sub, single and double, five rounding modes | 10,000,000 each | 1,205, 1,295; 1,455, 1,330 | [#8](https://github.com/lowRISC/muntjac/issues/8) |
| lowRISC/muntjac | FPU: fused multiply-add family, single and double | 400,000 each | 2,220 to 3,439 | #8 |
| lowRISC/muntjac | FPU: mul | 10,000,000 each | 0 values; underflow flag 53,406 and 69,672 | #8 |
| lowRISC/muntjac | FPU: div, sqrt; `muntjac_mul`, `muntjac_mul_fast`, `muntjac_div` | 400,000 each; about 500,000 per integer operation | 0 | |
| [rsd-devel/rsd](https://github.com/rsd-devel/rsd) | develop: FMA, add, sub, mul, div, sqrt, conversions, compares, five rounding modes, flags | 162,240,000 | 0 | |
| rsd-devel/rsd | master: FMUL | 3,120,000 | 22,818 | upstream #92, fixed on develop |
| [bluespec/Flute](https://github.com/bluespec/Flute) | FBox, checked-in RV64 Verilog: add, sub, mul, single and double, five rounding modes | 10,000,000 each | 339,869 to 698,070 | Bluespec library fix bsc #808 is later than the checked-in Verilog |
| bluespec/Flute | FBox: fused multiply-add, conversions, min/max | 40,000 per operation | see below | Flute #64, #65; Piccolo #23, #25, #26; bsc #1183 |
| bluespec/Flute | integer multiply/divide box, RV64 and RV32 | about 500,000 per operation | 0 | |
| [stnolting/neorv32](https://github.com/stnolting/neorv32) | Zfinx FPU, five rounding modes | 987,401 | 1,004 | [#1689](https://github.com/stnolting/neorv32/issues/1689) |
| stnolting/neorv32 | multiply/divide unit, serial and fast | 2,000,000 per variant | 0 | |
| [chipsalliance/Cores-VeeR-EH2](https://github.com/chipsalliance/Cores-VeeR-EH2) | 1/2/3/4-bit dividers, XLEN 64 | 1,000,000 each | 12,200 to 13,600 each | [#60](https://github.com/chipsalliance/Cores-VeeR-EH2/issues/60) |
| chipsalliance/Cores-VeeR-EH2 | all five dividers at XLEN 32, legacy at XLEN 64 | 4,000,000 each | 0 | |
| chipsalliance/Cores-VeeR-EL2 | all five dividers, with cancels | 4,000,000 each | 0 | |
| chipsalliance/Cores-VeeR-EH1 | divider, fast path on and off | 4,000,000 each | 0 | |
| [BrunoLevy/learn-fpga](https://github.com/BrunoLevy/learn-fpga) | PetitBateau FPU: FCVT.S.WU | 54,099 | 19,340 | [#185](https://github.com/BrunoLevy/learn-fpga/issues/185) |
| BrunoLevy/learn-fpga | PetitBateau: FEQ, FLT, FLE | 77,717 | 513 | #185 |
| BrunoLevy/learn-fpga | PetitBateau: add, sub, mul, fused, FCVT.W[U].S, min/max, sign injection | 1,200,000 | 0 | reference follows the documented deviations |
| [YosysHQ/picorv32](https://github.com/YosysHQ/picorv32) | `picorv32_pcpi_fast_mul`, `EXTRA_INSN_FFS = 1` | 1,000,000 | 702,633 | repository archived |
| YosysHQ/picorv32 | `picorv32_pcpi_div`, `picorv32_pcpi_mul`, `picorv32_pcpi_fast_mul` at its defaults | 2,000,000 each | 0 | |
| ultraembedded/biriscv, ultraembedded/riscv | divider, multiplier | 2,000,000 each | 0 | |
| [openhwgroup/cvfpu](https://github.com/openhwgroup/cvfpu) | `fpnew_top`: DIV on FP16ALT, five rounding modes | 5,000,000 | 9,752; flags only on 24,577 more | [#169](https://github.com/openhwgroup/cvfpu/issues/169), cause and fix |
| openhwgroup/cvfpu | merged ADDMUL unit: ADDS into a format with a narrower exponent, eight format pairs | 80,000,000 | 11,602,774 | [#195](https://github.com/openhwgroup/cvfpu/issues/195) |
| openhwgroup/cvfpu | fused multiply-add, add, sub, mul in both ADDMUL units and every format pair; DIV, SQRT in FP64, FP32, FP16; conversions, compares, min/max, sign injection, classify; five formats | 1,900,000,000; 691,564,032 more that cover small formats completely | 0 | |
| [openhwgroup/cva5](https://github.com/openhwgroup/cva5) | `fp_unit`: div and sqrt, single and double, requests issued back to back | 1,000,000 each | no answer to 67,439 and 37,932 divisions, 54,971 and 39,437 square roots | [#34](https://github.com/openhwfoundation/cva5/issues/34) |
| openhwgroup/cva5 | `fp_unit`: FSQRT.D on operands whose root is a 29-bit number plus less than 2^-55 of it, five rounding modes | 5,000,000 | 556,146; flags only on 2,224,584 more | [#35](https://github.com/openhwfoundation/cva5/issues/35) |
| openhwgroup/cva5 | `fp_unit`: FMUL.S and FCLASS.S on registers that are not NaN-boxed | 288,000; 518,400 | 140, flags only on 560 more; 14,400 | [#36](https://github.com/openhwfoundation/cva5/issues/36) |
| openhwgroup/cva5 | `fp_unit`: add, sub, fused multiply-add, FMUL.D, div and FSQRT.S one at a time, conversions, compares, min/max, sign injection, moves | 5,000,000 per operation and precision | 0 | |
| T-Head E906 | `pa_fpu_top`: div, sqrt, mul, add, sub, fused multiply-add, conversions | 1,100,000 per operation, five rounding modes; 10 to 20 million more for each of div, sqrt, mul, add | 0 values | underflow flag, reported |
| T-Head C906 | `aq_vpu_top`: the same operations in double, single and half | 1,100,000 per operation and format | 0 values | underflow flag, not reported for C906 |
| T-Head C910 | `ct_vfdsu_top`: div, sqrt in double, single and half | 1,100,000 per operation and format; 30 million more in double and single | 0 values | underflow flag, reported |
| [GRLIB](https://www.gaisler.com/grlib-ip-library) NOEL-V, 2026.3-b4301 | `nanofpunv` at its issue and commit interface: 29 F and D operations, single and double, five rounding modes | 4,384,000 | 24, all double fused multiply-add | reported to Gaisler, [cause and fix](noelv) |
| GRLIB NOEL-V | `nanofpunv`: an instruction issued in the cycle after an unissue | 43,008 aimed pairs; 30,000 random pairs | 1,600; 43 | reported, [cause and fix](noelv) |
| GRLIB NOEL-V | the whole core `cpucorenv`, HP, GP and GP-lite: a multiply or fused multiply-add at the target of a mispredicted branch | one program, [`flush.S`](noelv/flush.S) | wrong in each configuration | same report |
| IEEE 1076 `float_pkg`, the float package of the VHDL standard as the IEEE publishes it and GHDL and NVC ship it | add, subtract, multiply, divide, sqrt, mac, reciprocal, resize, dividebyp2, scalb and the conversions with integers; float16, float32, float64, float128; four rounding styles | 3,439,564 | 371,873, and 1,302 stop the simulator; with the default rounding 38,608 of 860,720 | reported to the IEEE working group as [#388](https://gitlab.com/IEEE-P1076/VHDL-Issues/-/work_items/388), GHDL [#3486](https://github.com/ghdl/ghdl/issues/3486) and NVC [#1758](https://github.com/nickg/nvc/issues/1758), [cause and patch](ieee-float-pkg) |
| IEEE 1076 `float_pkg` | every operand of a 7-bit format, and every operand pair of a 10-bit one | 8,692,326; 17,340,682 | 1,271,619; 883,716 | 0 with the patch |
| IEEE 1076 `fixed_pkg`, the fixed-point package of the same standard | every operand of six pairs of small index ranges, unsigned and signed, in every arithmetic operation | 751,418 | 41,026, all in division: about one quotient in twenty is not the nearest value with the default settings | [cause and patch](ieee-float-pkg#the-fixed-point-package), same report |
| [antonblanchard/microwatt](https://github.com/antonblanchard/microwatt), the OpenPOWER core | `fpu` at its port: 37 floating-point instructions under seven settings of the FPSCR exception enables, four rounding modes | 155,400 | 55, all in FPRF: an enabled underflow whose rounding carries is classed as denormalized | [#482](https://github.com/antonblanchard/microwatt/issues/482), [cause and fix](microwatt) |
| antonblanchard/microwatt | `fpu`: `fcfidus` on random 48-bit integers, four rounding modes | 80,000 | 7,470 values; the inexact bit missing on 19,928 | reported by others as [#476](https://github.com/antonblanchard/microwatt/issues/476); the range and the rates are added there |
| antonblanchard/microwatt | `fpu`: 43 instructions with every exception disabled, with the fix of #476 | 344,000 | 0 | |
| antonblanchard/microwatt | `fpu`: 43 instructions starting from a filled FPSCR; the record forms | 90,300; 9,030 | 0 | |
| antonblanchard/microwatt | `fpu`: the twelve integer divisions and remainders, OE and Rc both ways | 600,000 | 0 | |

## Reproducers

**dawsonjon/fpu `double_divider`.** Line 266 tests `z_m == 53'hffffff` before the rounding carry: the 24-bit constant of the single-precision divider.
A subnormal quotient whose shifted significand is `0xffffff` and rounds up is packed as a normal number.

```
0x02fffffff0000000 / 0x44a0000000000000    IEEE 0x0000000001000000 (8.289046e-317)    core 0x0020000001000000 (4.450148e-308)
```

The core returns 2^29 times the quotient. 66 public files on GitHub carry the line.

**dawsonjon/fpu `double_to_float`.** The 23-bit fraction is rounded on its own. The carry out of an all-ones fraction is dropped, ties never round up, and a value that rounds up to the smallest normal number returns zero.

```
0x3fefffffffffffff (1 - 2^-53)     IEEE 0x3f800000 (1.0)     core 0x3f000000 (0.5)
0x3ff0000030000000                 IEEE 0x3f800002           core 0x3f800001
0x380fffffffffffff                 IEEE 0x00800000           core 0x00000000
0x47effffff0000000                 IEEE 0x7f800000 (inf)     core 0x7f7fffff
```

**OpenCores `double_fpu`.**

```
add  0xe0ab933dc7aee14b + 0x60ab933dc7aee14b    IEEE +0                     core -0                    476 of 20,000
add  0x42f44ede50ad8e4a + 0xbfcdcc7f78569a3a    IEEE 0x42f44ede50ad8e46     core 0x42f44ede50ad8e47    429 of 20,000, one unit in the last place
mul  0xe98fffffffffffff * 0x8000000000000001    IEEE 0x266fffffffffffff     core 0x27b0000100000000    49 of 20,000, subnormal operand
div  0x00227c410bf31219 / 0x6b7159a6c8bec055    IEEE 0x0000000000000000     core 0x0000000000000001    903 of 20,000
```

**OpenCores `fpu`.** Infinities of opposite sign.

```
mul  0x7f800000 * 0xff800000    IEEE 0xff800000 (-inf)    core 0xffc00001 (NaN)
div  0x7f800000 / 0xff800000    IEEE NaN                  core 0xff800000 (-inf)
```

**OR1200 `or1200_fpu_arith`.**

```
mul  0x00129b1e * 0x3fde55f8    IEEE 0x00205187    core 0x0040a30e    twice the product; 101 of 20,000 with a subnormal operand
mul  0x46ffffff * 0x8000001f    IEEE 0x800f8000    core 0x800001f0
div  0x00717f69 / 0xff40f8f5    IEEE 0x80000000    core 0x80969150    45 of 20,000 with a subnormal dividend
mul  0xb4800000 * 0x0b7fffff    IEEE 0x80800000    core 0x80000000    rounds up to the smallest normal
```

**OpenRISC `pfpu32` and `pfpu_marocchino`.** The overflow branch of the rounding stage returns infinity in every mode. Toward zero, and toward the infinity of the other sign, IEEE 754 returns the largest finite number.

```
mul  0x7f7fffff * 0x40000000, toward zero    IEEE 0x7f7fffff    core 0x7f800000 (inf)
mul  0xff7fffff * 0x40000000, toward +inf    IEEE 0xff7fffff    core 0xff800000 (-inf)
```

**OpenRISC `pfpu_marocchino`, after a division by zero.** The divider holds its divide-by-zero output until its next result, and the rounding stage latches it for whatever operation arrives (`pfpu_marocchino_rnd.v`, line 266).

```
div 1.0 / 0.0    +inf, DZF    correct
add 1.0 + 1.0    expected 0x40000000    core 0x7f800000 (inf), DZF
mul 3.0 * 2.0    expected 0x40c00000    core 0x7f800000 (inf), DZF
```

Fix: `s0o_div_dbz <= div_rdy_i & div_dbz_i;`. 0 wrong of 15,680,000 after both fixes.

**BaseJump STL `bsg_fpu_add_sub`.** A zero operand is given a hidden 1 (line 117); the zero flags of the preprocess module are wired and never read. An exact zero sum takes the sign of the first operand.

```
add  0x00000000 + 0x00000000    IEEE 0x00000000    core 0x00800000 (smallest normal)
add  0x0c7fffff + 0x80000000    IEEE 0x0c7fffff    core 0x0c7ffffe
add  0xbf800000 + 0x3f800000    IEEE 0x00000000    core 0x80000000 (-0)
```

**BlackParrot `bp_be_pipe_aux`.** An integer is converted to double and the double is then rounded to single, so `fcvt.s.l` and `fcvt.s.lu` round twice. To nearest, the result is one unit in the last place off for integers above 2^53 that sit beside a halfway point of the single. About one random 64-bit integer in 2^28 is such a number.

```
fcvt.s.l  0x4000004000000001 (2^62 + 2^38 + 1)    IEEE 0x5e800001    core 0x5e800000
fcvt.s.l  0x400000bfffffffff                      IEEE 0x5e800001    core 0x5e800002
```

The fix hands the integer to the rounding stage unrounded. 0 wrong of 2,000,000 after it. Everything else in the F and D extensions, and RV64M, is right: the run goes through the core's own decoder, reservation stage and execution pipes.

**lowRISC muntjac FPU.** A zero operand is decoded with a placeholder magnitude, and the sum computed from it can cancel against the other operand. The double-precision fused multiply-add has no guard bits under the 106-bit product.

```
fadd.d   0 + 0x8008000000000000                                           expected 0x8008000000000000    core 0x8000000000000000
fmadd.d  0x3fefffffffffffff * 0x3fefffffffffffff + 0xbff0000000000000     expected 0xbcb0000000000000    core 0xbcafffffffffffff
fmul.d   0x3ff0000000000001 * 0x000fffffffffffff                          flags expected NX              core UF|NX
```

**Bluespec Flute FBox**, the Verilog checked into the repository. Round to nearest, ties away, rounds every inexact result away from zero. The double-precision fused multiply-add rounds the product before the add.

```
fadd.d   RMM  0x3ff0000000000000 + 0x3c80000000000000 (1 + 2^-55)                     expected 0x3ff0000000000000    core 0x3ff0000000000001
fmadd.d  RNE  0x3ff0000000000001 * 0x3ff0000000000001 + 0xbff0000000000002            expected 0x3970000000000000 (2^-104)    core 0x3c90000000000000 (2^-54)
fcvt.w.d RMM  0x4006000000000000 (2.75)                                               expected 3                     core 2
```

**neorv32 Zfinx FPU.** The float-to-integer path drops the mantissa bit shifted out for inputs in (0.5, 1), so 0.5 + 1 ulp looks like a tie. In round-down mode the zero sum of two zeros takes the wrong sign.

```
fcvt.w.s  0x3f000001 (0.5 + 2^-24)    expected 1     core 0
fsub.s    (+0) - (+0), round down     expected -0    core +0
```

**VeeR EH2, XLEN 64.** The leading-sign count of an all-ones operand is 0 in the 64-bit table (31 in the 32-bit one), so a divisor of -1 skips too many iterations. RV64 on EH2 is in progress upstream.

```
DIV  0x0000000000000010 / 0xffffffffffffffff    expected 0xfffffffffffffff0    1-bit divider 0xfffffffffffffffd
DIV  0x8000000000000000 / 0xffffffffffffffff    expected 0x8000000000000000    4-bit divider 0x00000000000008ff
```

**FemtoRV PetitBateau.**

```
fcvt.s.wu  0x80000000         expected 0x4f000000 (2^31)    core 0x4f800000 (2^32)
feq(+0, -0)                   expected 1                    core 0
0x00800000 / 0x00800006       expected about 0x3f7ffff4     core 0x3ffffff4, twice the quotient
0x3f000000 / 0x7f7fffff       expected 0 (flushed)          core 0x7f800000 (inf)
```

**picorv32 `picorv32_pcpi_fast_mul`, `EXTRA_INSN_FFS = 1`.** The registered instruction-valid stays high one clock after `pcpi_valid` drops; the multiplier restarts on stale operands. The core's own instance uses the defaults, which are right.

```
mul x5, 3, 5; mul x6, 7, 11; mul x7, 3, 11    expected 15, 77, 33    core 15, 15, 33
```

Fix: `EXTRA_INSN_FFS ? (pcpi_insn_valid_q && pcpi_valid) : pcpi_insn_valid` at line 2354. 0 wrong of 1,000,000 after.

**CVFPU `fpnew_top`, DIV on FP16ALT.** In the vendored C910 divider the skip threshold for FP16ALT is the binary32 constant, `12'hf6a` where `12'hf7a` belongs, and the default entry of the FP16ALT subnormal table is zero. A quotient below 2^-134 returns zero without flags.

```
0x0d00 / 0x5080 (2^-135)    expected 0x0000 UF|NX, toward +inf 0x0001 UF|NX    core 0x0000, no flags, every mode
```

Fix: two lines. 0 wrong of 20,000,000 after. The patch, a vector generator and a testbench are in [`cvfpu/`](cvfpu).

**CVFPU merged ADDMUL unit, ADDS into a narrower format.** The addend exponent, rebiased for the destination, goes below 1 and is truncated into the exponent field (`fpnew_fma_multi.sv`, line 777).

```
ADDS FP64 to FP32    (+0) + 0x37e0000000000000 (2^-129)    expected 0x00100000    core 0x7f000000 (2^127), no flags
```

**CVA5 `fp_unit`.** The divider and the square-root unit accept a request in the cycle the previous result is acknowledged, and in that cycle the acknowledge clears the flag that a zero, infinity or NaN result needs to complete. The square-root core's working registers are two bits narrower than its last steps need.

```
fdiv.d   3.0 / 2.0, then 0.0 / 2.0 in the first free cycle    expected 1.5, 0.0                          core 1.5, then no answer
fsqrt.d  0x400ffffff6000001                                   expected 0x3ffffffffb000000 NX,            core 0x3ffffffffb000000, no flags, every mode
                                                              toward +inf 0x3ffffffffb000001 NX
fclass.s 0x0000000000000000 (not NaN-boxed)                   expected 0x200                             core 0x220
```

Fix: three patches in [`cva5/`](cva5), with a bit-true model of the square-root core. No missing answer and 0 wrong after them.

**T-Head E906, C906, C910.** Values are right in every run. The underflow flag is not raised when a tiny inexact result rounds up to the smallest normal number.

```
fdiv.s  0x00ffffff / 0x40000000    result 0x00800000    IEEE flags UF|NX    core flags NX
```

**NOEL-V, GRLIB 2026.3-b4301.** Two defects in the float unit `nanofpunv`. A double fused multiply-add that subtracts a product ending in a run of ones from a larger addend is rounded as exact. And when an instruction is unissued while the multiplier runs and the next one is issued a cycle later, a partial product of the first stays in the accumulator; on the whole core that is a multiply behind a mispredicted branch and a multiply or fused multiply-add at the target.

```
fnmsub.d, round up    16 - (1 + 2^-52) * (1 - 2^-52)                     expected 402e000000000001      core 402e000000000000
at a branch target    fmul.d   3.0 * 5.0, round up                       expected 402e000000000000      core 402e000000000001, NX
at a branch target    fmsub.d  3.0 * 5.0 - 15.0, round to nearest        expected 0                     core 3affff0000000000 (1.65e-24), no flags
```

Fix: two patches in [`noelv/`](noelv), with the two programs and a testbench for the whole core in GHDL. 0 wrong after them.

**IEEE 1076 `float_pkg`.** The float package of the VHDL standard, in the IEEE's own source, which GHDL and NVC ship unchanged. With its own settings, round to nearest and three guard bits, the square root is a fixed number of Newton steps with no sticky bit, the multiply-accumulate subtracts the larger number from the smaller when the product and the addend have the same exponent, and every result's exponent is cut to two bits more than the target format's before its range is decided.

```
sqrt (2.0) in float64                   expected 3FF6A09E667F3BCD      package 3FF6A09E667F3BCC
mac (-6.0, -1.0, -5.0)                  expected 1.0                   package -15.0
resize (2.0**-512 in float64, 8, 23)    expected 0.0                   package 1.0
divide (6.0, 3.0, round_inf)            expected 2.0                   package 2.0000002
```

Fix: one patch to the package body in [`ieee-float-pkg/`](ieee-float-pkg), with the exact reference and a testbench for GHDL and NVC. 0 wrong after it in 32,470,838 calls.

## Your block

One arithmetic block of yours, audited this way: 2,500 USD, fixed.

You send the RTL and the function it implements. You receive the vector counts, every mismatch reduced to a one-line reproducer with the faulty line, and the fix.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology
