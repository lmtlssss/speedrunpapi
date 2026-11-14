# `llvm::APFloat`, the small formats

`APFloat` is LLVM's software floating point. Clang, the optimizer and MLIR fold constants with it. Beside the IEEE formats it has the 8-, 6- and 4-bit floats of machine-learning accelerators: `Float8E5M2`, `Float8E5M2FNUZ`, `Float8E4M3`, `Float8E4M3FN`, `Float8E4M3FNUZ`, `Float8E4M3B11FNUZ`, `Float8E3M4`, `Float8E8M0FNU`, `Float6E3M2FN`, `Float6E2M3FN`, `Float4E2M1FN`, and on main `Float8E5M3FNU`. An 8-bit format has 256 values, so every operand pair of an operation can be run, and every operand triple of the fused multiply-add.

Two builds were run: release 23.1.4 as Homebrew installs it, and main at commit [`11a7e80b`](https://github.com/llvm/llvm-project/commit/11a7e80b89a8b824d8d431fdbf19d4cb98e077db) of 14 November 2026 with assertions on.

[`apf.cpp`](apf.cpp) calls the library on every operand and prints the class, the bit pattern and the status it returns. [`apref.py`](apref.py) reads the value of every bit pattern from the library's own decoding and computes the rest with integers: the exact result, rounded once to the precision and least exponent of the format in the mode asked for, with overflow by the rule of IEEE 754. Where a format has no infinity, `APFloat.h` says a NaN comes back in its place. Where a format has no way to write the result and the header does not say what happens, the case is counted and not judged.

## Release 23.1.4

Eleven formats, the five rounding modes.

| operation | results | wrong |
| --- | --- | --- |
| `add`, `subtract`, `multiply`, `divide`, every operand pair | 2,663,680 each | 0 |
| `fusedMultiplyAdd`, every operand triple | 673,730,560 | 0 |
| `remainder`, `mod`, `compare`, every operand pair | 532,736 each | 0 |
| `convert` between the eleven formats, binary16 and bfloat, every value | 7,995,840 | 25 |
| `convertToInteger` to 1, 4, 8 and 16 bits, signed and unsigned | 87,680 | 0 |
| `convertFromAPInt`, every 8-bit and 12-bit integer, signed and unsigned | 478,720 | 0 |
| `roundToIntegral` | 10,960 | 1,366 |
| `scalbn`, every value and every exponent that keeps it in reach | 1,113,520 | 0 |
| `next` up and down | 4,384 | 0 |
| `ilogb`, `getExactLog2Abs`, `getExactInverse`, `isDenormal`, `isNormal`, `isSmallest`, `isSmallestNormalized`, `isLargest` | 2,192 values | 0 |
| all | 695,676,784 | 1,391 |

1,843,563 of the results are not judged.

The 1,391 are two defects LLVM already has on record.

`roundToIntegral` on `Float8E3M4` and `Float6E2M3FN`. The routine adds and subtracts 2^(p-1), and these two formats cannot hold that number. `Float8E3M4` returns NaN for every finite value except zero. `Float6E2M3FN` returns zero, for 1.0 too. That is 1,366 of the 1,600 calls on the two formats. `isInteger` goes through the same routine. With assertions on, main stops at `assert(fs == opOK)`. It is [llvm/llvm-project#224353](https://github.com/llvm/llvm-project/issues/224353), and a fix is open as [#240204](https://github.com/llvm/llvm-project/pull/240204). With that change on main, `roundToIntegral` on the twelve formats, binary16 and bfloat is right on 667,081 of 667,600 calls; the other 519 are not judged.

`convert` of the NaN of `Float8E8M0FNU` to an IEEE format returns a value whose class is NaN and whose bits are those of infinity, `7ff0000000000000` in binary64. Five formats and five modes make the 25; binary32 and binary64 do the same. Main has had the fix since August ([#214919](https://github.com/llvm/llvm-project/pull/214919)); 23.1.4 does not.

## Main

Twelve formats. 24,288,320 results outside the fused multiply-add, and 170,414,080 fused multiply-adds on `Float8E4M3`, `Float8E3M4` and the 6- and 4-bit formats.

13,248 of them end in an assertion: 1,408 `roundToIntegral` calls on the two formats above, and 11,840 conversions of a negative infinity or a negative NaN to the two formats without a sign (open fix: [#230086](https://github.com/llvm/llvm-project/pull/230086)). Every other judged value is right.

## The underflow flag

`APFloat.h` says "underflow tininess is detected after rounding". By IEEE 754-2019, 7.5, a result is then tiny when, rounded to the precision of the format as though the exponent range were unbounded, it lies strictly between ±2^emin, and a tiny result that is inexact raises underflow.

`IEEEFloat::normalize` takes "the rounded result is a normal number" to mean "not tiny". A result in the binade below the smallest normal number that rounds up to it returns `opInexact` alone:

```cpp
APFloat P(0x1.fffffffffffffp-1);                 // 1 - 2^-53
APFloat::opStatus St = P.multiply(APFloat(0x1p-1022), APFloat::rmNearestTiesToEven);
// P is 0x1p-1022 and St is opInexact. opUnderflow | opInexact is right.
```

The exact product is `0x1.fffffffffffffp-1023`. It fits in 53 bits, so the rounding with an unbounded exponent leaves it below 2^-1022. [`issue_underflow.cpp`](issue_underflow.cpp) is this example with binary32 and binary16 beside it. [`uf_hw.c`](uf_hw.c) does the multiplication on the processor: an Apple M1 raises underflow for it, and so does the x86-64 machine of this repository's [workflow](../../../.github/workflows/apfloat.yml), which detects tininess after rounding and stays silent on the second product of that file, the one that reaches 2^-1022 in 53 bits.

It is the last test of `normalize`:

```cpp
  /* The normal case - we were and are not denormal, and any
     significand increment above didn't overflow.  */
  if (omsb == semantics->precision)
    return opInexact;
```

A denormal that the increment has just carried up to the smallest normal number arrives here as well.

On main, in the twelve formats and the five rounding modes:

| | results | `opInexact` where underflow is due |
| --- | --- | --- |
| `multiply`, every operand pair | 2,991,360 | 12,660 |
| `divide`, every operand pair | 2,991,360 | 11,044 |
| `convert` between the twelve formats, binary16 and bfloat | 8,678,800 | 8,149 |
| `fusedMultiplyAdd`, every operand triple of five formats | 170,414,080 | 65,356 |

The values are right in all of them. A sum or a difference that small is exact, so `add` and `subtract` do not show it. The release has it the same way: 224,229 of its results above.

[`underflow.patch`](underflow.patch) is a fix for main with a unit test: 131 lines added and 21 removed, 42 and 21 of them in `APFloat.cpp`. `normalize` looks, in the binade below the smallest normal number, at whether the rounding to full precision carries up to it. `convert` no longer cuts a subnormal source down to the target's least exponent before `normalize` sees it. With the patch:

- every status in the sweep above agrees with the rule, except the overflow flag of the next section;
- the two builds were compared line by line. Conversions: 8,670,428 results identical, 8,372 with the status changed from `opInexact` to `opUnderflow | opInexact`, nothing else. Those are the 8,149 and 223 negative operands converted to a format without a sign, which are not judged. The arithmetic, `remainder`, `mod`, `roundToIntegral`, `next`, `scalbn` and the integer conversions: 14,985,096 identical, 23,704 with that status change, nothing else;
- the 325 tests of LLVM's `APFloatTest.cpp` pass before and after. The new test fails on main in 8 of its expectations and passes with the patch ([`uf_cases.cpp`](uf_cases.cpp) is its table as a program).

`convertFromString` on a decimal string is not changed. `roundSignificandWithExponent` cuts a denormal down to the least exponent itself, and the bits that decide are gone before `normalize` is called: `2.2250738585072012e-308` still returns `opInexact`. A hexadecimal string goes through `normalize` whole and is fixed ([`uf_strings.cpp`](uf_strings.cpp)).

The patch changes LLVM's source and is offered under LLVM's licence, Apache-2.0 with LLVM exceptions.

## The overflow flag

When an overflow is rounded to the largest finite number, in the directed modes, the status is `opInexact` without `opOverflow`: 33,102,374 results of the release sweep. That is [llvm/llvm-project#220018](https://github.com/llvm/llvm-project/issues/220018), with a fix open as #220020.

## What is not judged

The three formats without infinity or NaN (`Float6E3M2FN`, `Float6E2M3FN`, `Float4E2M1FN`): an overflow returns the largest finite number. A division by zero returns a value whose class is infinity, which the format cannot write; its bits read as zero in the release, and main stops at `llvm_unreachable` when they are read. 0/0 and a `remainder` or `mod` by zero return class NaN with the bits of zero in the release; main stops inside the operation. [#182433](https://github.com/llvm/llvm-project/issues/182433) is this through `convert`.

`Float8E8M0FNU` has no zero and no sign: a zero result comes back as the least positive number, and a negative one is not defined.

`roundToIntegral` where the integer is above the largest finite number, 15.5 in `Float8E3M4` and 7.5 in `Float6E2M3FN`.

## Run it

```sh
sh build.sh                                   # apf, against the installed LLVM (Homebrew: /opt/homebrew/opt/llvm)
F=E5M2,E5M2FNUZ,E4M3,E4M3FN,E4M3FNUZ,E4M3B11FNUZ,E3M4,E8M0FNU,E3M2FN,E2M3FN,E2M1FN
python3 apref.py ./apf out $F bin,remmod,rint,next,cmp,toint,fromint,scalbn,misc
CONV_TARGETS=$F,half,bfloat python3 apref.py ./apf out $F,half,bfloat conv
python3 apref.py ./apf out $F fma             # 671 million triples for the eight 8-bit formats
python3 agg.py out
```

`apref.py` prints one line per run that has a wrong result and writes the operands to `out/*.bad`. `agg.py` adds the runs up: totals by operation, what was not judged and what the library returned there, and the statuses that differ.

For main, `build.sh trunk DIR` builds `apf_trunk` from the `APFloat.cpp` and the headers of an LLVM checkout in `DIR`, with assertions on; the generated `llvm/Config` headers and the rest of `LLVMSupport` come from the installed library. A case that ends in an assertion is caught and printed as a signal. `build_ut.sh DIR apf_trunk` builds LLVM's own `APFloatTest.cpp` against the same object.

The patch, on copies of the two files it changes:

```sh
mkdir -p patched/llvm/lib/Support patched/llvm/unittests/ADT
cp DIR/llvm/lib/Support/APFloat.cpp patched/llvm/lib/Support/
cp DIR/llvm/unittests/ADT/APFloatTest.cpp patched/llvm/unittests/ADT/
patch -p1 -d patched < underflow.patch
sh build.sh trunk DIR apf_fix patched/llvm/lib/Support/APFloat.cpp
sh build_ut.sh DIR apf_fix patched/llvm/unittests/ADT/APFloatTest.cpp && ./ut_apf_fix --gtest_brief=1
F=$F,E5M3FNU
python3 apref.py ./apf_fix out_fix $F bin,remmod,rint,next,cmp,toint,fromint,scalbn,misc
python3 diffbin.py ./apf_trunk ./apf_fix $F bin,remmod,rint,next,toint,fromint,scalbn
```
