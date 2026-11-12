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
| T-Head E906 | `pa_fpu_top`: div, sqrt, mul, add, sub, fused multiply-add, conversions | 1,100,000 per operation, five rounding modes; 10 to 20 million more for each of div, sqrt, mul, add | 0 values | underflow flag, reported |
| T-Head C906 | `aq_vpu_top`: the same operations in double, single and half | 1,100,000 per operation and format | 0 values | underflow flag, not reported for C906 |
| T-Head C910 | `ct_vfdsu_top`: div, sqrt in double, single and half | 1,100,000 per operation and format; 30 million more in double and single | 0 values | underflow flag, reported |

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

**T-Head E906, C906, C910.** Values are right in every run. The underflow flag is not raised when a tiny inexact result rounds up to the smallest normal number.

```
fdiv.s  0x00ffffff / 0x40000000    result 0x00800000    IEEE flags UF|NX    core flags NX
```

## Your block

One arithmetic block of yours, audited this way: 2,500 USD, fixed.

You send the RTL and the function it implements. You receive the vector counts, every mismatch reduced to a one-line reproducer with the faulty line, and the fix.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology
