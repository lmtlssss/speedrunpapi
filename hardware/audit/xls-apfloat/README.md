# XLS `apfloat`

[`apfloat.x`](https://github.com/google/xls/blob/v0.0.0-11089-gc2639fac5/xls/dslx/stdlib/apfloat.x) is the floating-point library of [google/xls](https://github.com/google/xls), Google's high-level synthesis toolchain: add, multiply, fused multiply-add, the conversions and the rounding functions, written in DSLX for any exponent and fraction width, and compiled to Verilog. Release `v0.0.0-11089-gc2639fac5` of 13 November 2026 was run.

[`w.x`](w.x) instantiates the functions at four small sizes, `APFloat<3,2>`, `<4,3>`, `<3,4>` and `<5,2>`; the second and the last are the layouts of the 8-bit E4M3 and E5M2 formats. The [workflow](../../../.github/workflows/xls-apfloat.yml) turns each wrapper into a combinational Verilog module with XLS's own `ir_converter_main`, `opt_main` and `codegen_main`. [`xrun.py`](xrun.py) simulates every module on every value of its inputs and compares with [`xref.py`](xref.py): IEEE 754 to nearest even by integer arithmetic, with the differences the library documents (subnormal operands are zero and subnormal results are flushed where a function says so, one canonical NaN).

147 modules, 52,747,584 calls.

| functions | calls | wrong |
| --- | --- | --- |
| `add` (with and without the leading-zero anticipator), `sub`, `mul`; `eq_2`, `gt_2`, `gte_2`, `lte_2`, `lt_2`; `ceil`, `floor`, `trunc`, `round` in their variants; `to_int`, `to_uint`, `cast_to_fixed`; `cast_from_fixed_using_rne`; `ldexp`; `downcast`, `downcast_rne`, `upcast_with_denorms`, `upcast_daz`: 135 modules | 2,136,384 | 0 |
| `fma`, every operand triple of the four formats | 50,593,792 | 9,260,784 |
| `cast_from_fixed_using_rz`, every 8-bit and 12-bit integer | 17,408 | 12,165 |

Eight calls are not judged: `ceil`, `floor` and `round` of 15.5 in `APFloat<3,4>`, where the integer is above the largest finite number.

Every finite result of `fma` is right. The wrong ones are of two kinds, and XLS's own interpreter fails the same cases ([`repro.x`](repro.x): 4 tests ran, 4 failed).

## `fma` returns infinity, or another NaN, where the result is NaN

`fma` builds its NaN with its own constant ([line 3655](https://github.com/google/xls/blob/v0.0.0-11089-gc2639fac5/xls/dslx/stdlib/apfloat.x#L3655)):

```
    let result_fraction =
        if is_result_nan { uN[FRACTION_SZ]:1 << (FRACTION_SZ - 4) } else { result_fraction };
```

`qnan()`, which the other functions return, has the fraction `1 << (FRACTION_SZ - 1)`. With fewer than four fraction bits the shift amount wraps, the fraction is zero and the result is infinity:

```
APFloat<4,3>  fma(NaN, 1.0, 1.0)     78    +inf        7c is the NaN
APFloat<4,3>  fma(inf, 0.0, 1.0)     78
APFloat<5,2>  fma(NaN, 1.0, 1.0)     7c    +inf        7e is the NaN
```

2,621,116 of the 16,777,216 triples of `APFloat<4,3>`, 1,161,180 of `APFloat<5,2>` and 69,084 of the 262,144 of `APFloat<3,2>`.

With four or more fraction bits the result is a NaN whose quiet bit is clear, not the canonical one the documentation promises. In `APFloat<3,4>` that is `71` where `qnan()` is `78`, on 5,263,740 triples. At the standard widths ([`cases.v`](cases.v)):

```
binary32  fma(NaN, 1.0, 1.0)     7f880000      qnan() is 7fc00000
bfloat16  fma(NaN, 1.0, 1.0)     7f88
binary16  fma(NaN, 1.0, 1.0)     7c40
```

## `fma` returns +0 for a negative zero product added to a negative zero

`(1.0 * -0.0) + -0.0` is -0.0, and `add(-0.0, -0.0)` returns it. `fma` returns +0.0: binary32 `fma(3f800000, 80000000, 80000000)` is `00000000`. 29,696 triples of `APFloat<4,3>`, 106,496 of `APFloat<3,4>`, 7,808 of `APFloat<5,2>`, 1,664 of `APFloat<3,2>`.

## `cast_from_fixed_using_rz` overflows to infinity

Rounding toward zero carries an overflow to the largest finite number. 100000 to binary16 comes back `7c00`, infinity, where 65504 (`7bff`) is the result. `APFloat<4,3>` from a 12-bit integer returns infinity for all 3,585 integers of magnitude 256 or more. `cast_from_fixed_using_rne` is right to return infinity there.

## One thing the documentation leaves open

"Subnormal results are flushed to zero." A result below the smallest normal number that IEEE rounding carries up to it comes back as the smallest normal number from `mul` and `ldexp`, and as either that or zero from `fma`. Both are accepted here; `xrun.py` prints how often each occurs.

## Run it

The Verilog is an artifact of the workflow (`gh run download`, artifact `xls-apfloat-verilog`), or build it with a Linux XLS release as the workflow does.

```sh
python3 mkwrap.py w.x tops.txt                 # the wrappers and their list
python3 xrun.py v tops.txt out                 # every module on every input; needs Icarus Verilog
python3 fmaclass.py v 4 3 out                  # the fma differences of one format by operand class
iverilog -g2012 -o cases v/fma_8_23.v v/fma_8_7.v v/fma_5_10.v v/fma_4_3.v v/fma_5_2.v v/fromfixed_rz_5_10_32.v cases.v && vvp -n cases
```
