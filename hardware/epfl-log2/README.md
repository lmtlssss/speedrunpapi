# EPFL log2

`log2` is one of the ten arithmetic circuits of the [EPFL combinational benchmark suite](https://github.com/lsils/benchmarks): 32 inputs, 32 outputs, 32,060 AND nodes.
The suite keeps a list of the smallest known LUT-6 implementations.

| | LUT-6 | Levels |
| --- | --- | --- |
| Smallest published, `best_results/size/log2_size_2026.blif` | 5,986 | 300 |
| [`log2_size_2027.blif`](log2_size_2027.blif) | 4,099 | 138 |

The first row is the suite's table. The second is `nd` and `lev` from ABC `print_stats`; `&get -m; &ps` gives the same two numbers.
The netlist gives the benchmark's output on all 4,294,967,296 inputs.

## What the benchmark computes

The circuit has no description beyond its name. It computes this, for the input word x with bit 0 the first input:

```
A   = x[30:23]                                    eight bits, the table address

U   = (C2[A] + ((M2[A] * x) >> 32)) mod 2^40      read as two's complement
V   = (C1[A] + ((U * x) >> 31)) mod 2^41          read as two's complement
out = ((C0[A] + ((V * x) >> 31)) >> 4) mod 2^32
```

`>>` rounds toward minus infinity. `M2`, `C2`, `C1` and `C0` are tables of 256 entries in [`tables.json`](tables.json), with 36, 40, 39 and 36 bits.

With bit 31 set, the output is log2(x / 2^31) with 32 fraction bits.
The interval from 1 to 2 is cut into 256 segments and each segment has its own cubic, evaluated in Horner form with three truncations.
The variable of the cubic is t = x / 2^31 itself, the whole input, and not the offset inside the segment:

```
out / 2^32 = c0 + t * (c1 + t * (c2 + t * c3))  mod 1

M2 = c3 * 2^37        C2 = c2 * 2^36  (c2 is negative)        C1 = c1 * 2^36        C0 = (c0 mod 1) * 2^36
```

The coefficients are the cubic Taylor polynomial of log2 around the middle xm of the segment, written in powers of t:
c3 = 1 / (3 ln2 xm^3), c2 = -3 / (2 ln2 xm^2), c1 = 3 / (ln2 xm), c0 = log2(xm) - 11 / (6 ln2).
Every table entry is within 0.00001 of these values.

Bit 31 does not enter the tables. With bit 31 clear the output is the cubic of segment A at t below 1, modulo 2^32.

On 16,777,216 random inputs with bit 31 set, the output lies between 1.40 below and 0.47 above the true value, in units of the last bit, and equals the true value rounded down on 13,599,903 of them.

## The netlist

It is built from the formula, one bit heap per line of it.

- First product. With z = x mod 2^23, M2 * x = M2 * z + x31 * M2 * 2^31 + M2 * A * 2^23. The last term depends on A alone and joins C2 in one table of 47 bits. The multiplier that remains is 36 by 23 bits.
- U always has its two top bits set, so only 38 bits of it are built, and the top radix-4 digit of U stands for -4, -3, -2 or -1. No row is spent on the sign.
- V always lies between 2^36 and 5 * 2^36, so its top digit is 1, 2, 3 or 4 and two bits name it. No row is spent on the 39th bit.
- A row is a radix-4 digit times the input word, one LUT per bit. A digit of 3 needs x + 2x; the row bit takes the carry from the row bit below it, so no adder forms 3x.
- Each line of the formula throws its low bits away. The columns below the cut pass their carries upward and form no sum bit.
- Every final addition is one LUT per bit, with the carry recovered from the column below.

This gives 4,142 LUTs. ABC `mfs2`, `lutpack`, `&satlut` and `&mfs` then took it to 4,099.

## Check

[`check.c`](check.c) simulates the benchmark, the formula and the netlist on every input and counts the inputs where they differ. It needs a C compiler and nothing else.

```
cc -O3 -o check check.c -lpthread
./check <arithmetic/log2.aig of lsils/benchmarks> log2_size_2027.blif tables.json 8
```

```
benchmark: 32060 AND nodes. netlist: 4099 LUTs, at most 6 inputs each.
input words 0x00000000 to 0xffffffff (4294967296 words)
formula against benchmark: 0 differ
netlist against benchmark: 0 differ
```

The last argument is the number of threads. The run takes 21 minutes on seven threads of an Apple M1.
The same check runs on each change to this folder, in sixteen parts, against `log2.aig` of lsils/benchmarks commit `82d8cc6` ([workflow](../../.github/workflows/epfl-log2.yml)).
