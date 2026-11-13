# CVFPU

[openhwgroup/cvfpu](https://github.com/openhwgroup/cvfpu), branch `develop` at `532f0f8`, `fpnew_top` with its default parameters and with the merged ADDMUL unit.

## DIV on FP16ALT

A quotient below 2^-134 returns zero without flags. Upstream issue [#169](https://github.com/openhwgroup/cvfpu/issues/169) reports the symptom.

```
0x0d00 / 0x5080  =  2^-101 / 2^34  =  2^-135        a quarter of the smallest subnormal, 2^-133

mode   expected          develop
RNE    0x0000  UF|NX     0x0000  no flags
RTZ    0x0000  UF|NX     0x0000  no flags
RDN    0x0000  UF|NX     0x0000  no flags
RUP    0x0001  UF|NX     0x0000  no flags
RMM    0x0000  UF|NX     0x0000  no flags
```

Two lines of the FP16ALT patch to the vendored C910 divider cause it:

- `ct_vfdsu_srt.v`: `ex2_bfloat_id_nor_srt_skip` compares the quotient exponent with `12'hf6a`. That is -150, the constant of binary32. FP16ALT has 7 fraction bits and its constant is -134, `12'hf7a`.
- `ct_vfdsu_round.v`: the `default` entry of the FP16ALT subnormal table is `11'b0`. The double, single and half tables put the quotient bits there.

[`fp16alt_div_underflow.patch`](fp16alt_div_underflow.patch) changes the two lines.

| File | |
| --- | --- |
| [`fp16alt_div_vectors.py`](fp16alt_div_vectors.py) | Writes operand pairs with the expected result and flags for the five rounding modes. The quotient is a rational number, rounded once. Python, no packages. |
| [`fp16alt_div_vectors.txt`](fp16alt_div_vectors.txt) | 20,620 vectors: `fp16alt_div_vectors.py 4000 169`. 1,100 of the 4,124 operand pairs have a quotient below 2^-134. |
| [`tb_fp16alt_div.sv`](tb_fp16alt_div.sv) | Reads the vector file, drives `fpnew_top` and stops with `$fatal` when a result or a flag word differs. |

```
develop      20620 vectors, 151 with a wrong result, 91 with the right result and wrong flags
patched      20620 vectors, 0 with a wrong result, 0 with the right result and wrong flags
```

Run with Verilator 5: the sources of `Bender.yml`, `cf_math_pkg.sv`, `lzc.sv` and `rr_arb_tree.sv` of common_cells, and `tb_fp16alt_div.sv`, with `--binary --timing --top-module tb_fp16alt_div -DCOMMON_CELLS_ASSERTS_OFF`.

## ADDS into a format with a smaller exponent range

`ADDS` adds two operands of the source format and rounds into the destination format. With the merged ADDMUL unit and a destination whose exponent field is narrower than the source's, a sum at or below the destination's smallest normal number is wrong.

```
ADDS, FP64 to FP32:   (+0) + 0x37e0000000000000 (2^-129)

expected   0x00100000   exact, no flags
develop    0x7f000000   2^127, no flags, in every rounding mode
```

In `fpnew_fma_multi.sv` the addend exponent, rebiased for the destination, goes below 1 and is truncated into the exponent field.
[`adds_narrowing.patch`](adds_narrowing.patch) is a candidate fix: for such a request the addend with the larger exponent takes the product side, whose path denormalises.
[`adds_narrow_vectors.py`](adds_narrow_vectors.py) writes FP64 to FP32 vectors with expected results: 100,010 vectors, 11,227 with a wrong result on `develop`, 0 with the patch.

No RISC-V instruction is a narrowing add of this kind. A core that follows the instruction set does not issue it.
