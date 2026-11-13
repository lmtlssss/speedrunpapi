# NOEL-V

[GRLIB](https://www.gaisler.com/grlib-ip-library) GPL release `2026.3-b4301`, the float unit `nanofpunv` of the NOEL-V processor: first alone, driven at its issue, commit and unissue interface, then inside the whole core `cpucorenv` running a program from a memory on its AHB port.

## Fused multiply-add that subtracts

A double-precision fused multiply-add returns the truncated result in the directed rounding modes, and leaves the underflow flag clear, when the product is subtracted from a larger addend and its low bits are ones all the way down.

```
fnmsub.d, round up      16 - (1 + 2^-52) * (1 - 2^-52)      expected 402e000000000001, NX      2026.3-b4301  402e000000000000, NX
fmsub.d, round down     (1 + 2^-52) * (1 - 2^-52) - 16      expected c02e000000000001, NX      2026.3-b4301  c02e000000000000, NX
```

The product is 1 - 2^-104, one hundred and four ones. The exact result of the first line is 15 + 2^-104, so rounded up it is the next double above 15. [`fma.S`](fma.S) is that instruction as a program.

In `nf_muladd_xaddsub3` the bits of the smaller operand that were shifted out below the extended datapath, `r.inexact`, are taken as a borrow. The difference is then below the true value by less than one unit of its last kept bit, so it needs a sticky bit. `nf_muladd_xaddsub7` and `nf_muladd_xaddsub9` set the sticky bit from `r.inexact` for an addition only, `if r.addneg = '0'`. When the kept low bits of the difference are all zero, which is what a run of ones gives after the borrow, nothing else sets it and the result is rounded as exact. `nf_round` still raises the inexact flag, after the underflow decision has been made without it.

[`fma_subtract_sticky.patch`](fma_subtract_sticky.patch) sets the sticky bit for a subtraction too.

```
the unit alone                                                                          2026.3-b4301                        patched
29 F and D operations, single and double, five rounding modes, 4,384,000 instructions    24 wrong, all double fused multiply-add
fused multiply-add family, single and double, 800,000 instructions                       21 wrong, all double                0
```

## An instruction issued in the cycle after an unissue

When the integer unit unissues an instruction while the multiplier of the float unit is running, and issues the next float instruction in the following cycle, one partial product of the cancelled instruction is added into the new instruction's accumulator. A multiply then comes out inexact and one unit high in the last place. A fused multiply-add whose exact result is zero returns the stale bits.

On the whole core it takes a mispredicted branch. [`flush.S`](flush.S):

```
        bnez    t2, target          # taken, predicted not taken
        fmul.d  f10, f3, f3         # wrong path, f3 = 0x3fffffffffffffff
        ...
target: fmul.d  f11, f1, f2         # 3.0 * 5.0
```

```
instruction at the target                 expected                    2026.3-b4301              patched
fmul.d   3.0 * 5.0, round up              402e000000000000            402e000000000001, NX      402e000000000000
fmul.d   3.0 * 5.0, to nearest            402e000000000000            402e000000000000, NX      402e000000000000
fmadd.d  3.0 * 5.0 + 7.0, round up        4036000000000000            4036000000000001, NX      4036000000000000
fmsub.d  3.0 * 5.0 - 15.0, to nearest     0000000000000000            3affff0000000000          0000000000000000
```

3.0 * 5.0 - 15.0 comes back as 1.65e-24 with no flag raised.

These are runs of `cpucorenv` with the generics of `designs/noelv-generic` and that design's `grlib_config.vhd`, in the HP, GP and GP-lite configurations, on a memory with no wait states, straight after reset. With the wrong-path multiply replaced by a nop every line is right. The result depends on the cycle the unissue arrives in: with one more instruction in front of the target, or two wait states in this memory, the same program returns the right product, and other programs will meet the window at other latencies. Over the three configurations, 0 to 3 wait states, the four alignments and the first and last lines of the table, 18 of 96 runs are wrong on the release and none with the patch.

On an unissue `nanofpunv` goes to `nf_idle` and leaves `mulen` as the multiply state set it in that cycle, so `accen` follows one cycle later. `nf_idle` clears the accumulator. But an instruction issued in that idle cycle has the unit in `nf_flopr` one cycle later with `r.accen` still set, and `acc` takes `r.mulo`, a partial product of the unissued instruction. The multiply states start from the accumulator as they find it. The integer unit can issue that soon because `ready` goes high in the unissue cycle itself, and a float instruction waiting in register access moves to execute at the next edge. In a dual-issue configuration the instruction paired behind a mispredicted branch is issued with the branch and unissued three stages later (`me_fpu_flush` in `iunv.vhd`), and the first instruction of the right path reaches register access in the cycle of that unissue.

The float unit's signals in the run of `flush.S`, GP configuration, one line per clock cycle:

```
holdn  unissue  e_valid  ready   r.s        r.mulen  r.accen  r.acc
  0       1        0       0     nf_mul4       1        1     1ffdbff8     unissue of the wrong-path multiply waits for holdn
  1       1        0       1     nf_mul4       1        1     2ffb8000     taken here; ready is high in the same cycle
  1       0        1       0     nf_idle       1        1     0ffe7ff6     the multiply at the target is issued
  1       0        0       0     nf_flopr      0        1     00000000     nf_idle cleared acc; accen is still set
  1       0        0       0     nf_flop0      0        0     0fff8001     a partial product of the cancelled multiply
  ...
  1       0        0       0     nf_mul4       0        0     0fff8001     the new multiply starts from it
```

The wrong-path multiply was issued 15 cycles before its unissue was taken: instruction fetches held the pipeline for 12 of them, and the unit does not stop for `holdn`.

[`unissue_multiplier_pipeline.patch`](unissue_multiplier_pipeline.patch) clears `mulen`, `accen` and the two shift flags on an unissue.

```
the unit alone: an instruction unissued, the next one issued one cycle later                   2026.3-b4301      patched
every cycle of a multiply, fused multiply-add, divide, square root, add and conversion,
  followed by an instruction with an exact result, 43,008 pairs                                1,600 wrong       0
30,000 random pairs                                                                            43 wrong          0
```

The second instruction goes wrong when the first is unissued 7 to 22 cycles after its issue for a double multiply or fused multiply-add, 7 to 10 for a single multiply, and in 250 of the 446 cycles of a double square root. It never does after a divide, an add or a conversion, and never when the next issue comes two or more cycles after the unissue.

Among the 43 random pairs the second instruction is off by one unit in the last place or has a wrong inexact flag when it is a multiply, and is wrong in every bit when it is a fused multiply-add that cancels: one single-precision `fnmsub.s` with the exact result -0.0 returned ce800001, about -1.07e9.

## Running it

GHDL for the core and LLVM's `llvm-mc` and `llvm-objcopy` for the two programs.

```
sh build.sh /path/to/grlib-gpl-2026.3-b4301                             # analyses 94 files, a few minutes
sh run.sh fma.S                                                         # result 402e000000000000 flags 01
sh run.sh flush.S                                                       # result 402e000000000001 flags 01
sh run.sh flush.S 1 0 -DFCSR=0 "-DSECOND=fmsub.d f11, f1, f2, f5"       # result 3affff0000000000 flags 00

cp /path/to/grlib-gpl-2026.3-b4301/lib/gaisler/noelv/core/nanofpunv.vhd .
patch nanofpunv.vhd fma_subtract_sticky.patch
patch nanofpunv.vhd unissue_multiplier_pipeline.patch
sh build.sh /path/to/grlib-gpl-2026.3-b4301 nanofpunv.vhd
```

`build.sh` reads the release's own source lists and runs nothing of its build system. [`tb_core.vhd`](tb_core.vhd) is the testbench: `cpucorenv`, a 64 KiB memory on the AHB master port with a settable number of wait states, and a line printed for every write the program makes. `run.sh PROGRAM.S CFG WAITS` takes the configuration (1 GP, 0 HP, 6 GP-lite) and the wait states; `-DPAD=1` and `-DTPAD=1` move the branch and the target of `flush.S` by one instruction.

The single-issue GP configuration, `cfg = 2`, does not run in GHDL: a bound check fails at `iunv.vhd` line 16060, where the SPARROW block reads lane 1.

Everything else in the unit came out right in the 4,384,000 instructions: add, subtract, multiply, divide, square root, the conversions, the comparisons, minimum and maximum, sign injection, classify and the moves, in both precisions and all five rounding modes, and again with the same instructions in random order.
