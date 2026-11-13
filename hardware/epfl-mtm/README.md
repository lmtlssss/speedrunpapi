# EPFL sixteen, twenty, twentythree

The three largest circuits of the [EPFL combinational benchmark suite](https://github.com/lsils/benchmarks), 16 to 23 million AND gates each, as LUT-6 netlists of 13,000 LUTs.
Each netlist is proven equivalent to the EPFL original. The proof uses no solver and runs in minutes.

| Circuit | Inputs | Outputs | Original, AND gates | EPFL best LUT-6, 2026 | LUT-6 here | Levels |
| --- | --- | --- | --- | --- | --- | --- |
| sixteen | 117 | 50 | 16,216,836 | 3,282,958 | 13,092 | 134 |
| twenty | 137 | 60 | 20,732,893 | 4,166,467 | 13,079 | 134 |
| twentythree | 153 | 68 | 23,339,737 | 470,892 | 13,104 | 138 |

The LUT and level counts are `nd` and `lev` from ABC `print_stats` on [`sixteen.blif`](sixteen.blif), [`twenty.blif`](twenty.blif), [`twentythree.blif`](twentythree.blif).
The originals are the AIGER files of `EPFL_complete.tar.gz`, Zenodo record 2572934.

## What the circuits compute

Inputs 0 to 16 are a number x. The other inputs are two words A and B of n bits each, least significant bit first.

```
F(-1) = 1, F(0) = 0, F(i) = F(i-1) + F(i-2) mod 2^64
s(v)  = v if v < 2^63, else 0

X(x)   = s(F(x)) mod 2^n                      for 0 <= x <= N-2, else 0
Y(A,B) = OR of s(F(i+1)) mod 2^n over every i in 0 .. N-3
         with (A, B) = (s(F(i)), s(F(i-1))) mod 2^n

sixteen       out = X(x) OR Y(A,B)            n = 50, N = 100000
twenty        out = NOT (X(x) OR Y(A,B))      n = 60, N =  90000
twentythree   out = NOT (X(x) OR Y(A,B))      n = 68, N =  94000
```

It is a Fibonacci loop in signed 64-bit integers written out as a truth table: one row per index, one row per addition, a negative number stored as zero.
Y is on at 37,334, 33,715 and 35,181 points (A,B).
The EPFL netlists store these rows. The netlists here compute them.

The proof does not assume the rule. It reads X and Y off the original netlist as tables, and the rule is then checked against those tables.

## The netlists

**x half, 4,870 LUTs in sixteen.** x = 384 a + b. One table holds F(384 a) and F(384 a - 1), one holds F(b) and F(b+1) for b < 384, and

```
F(384 a + b) = F(384 a) F(b+1) + F(384 a - 1) F(b)
```

takes two multipliers. F(384 a) is a multiple of 512 and F(384 a - 1) is 1 more than a multiple of 256, so the multipliers are 55 and 56 bits wide.

**Index, 1,398 LUTs.** A row of Y is found from the low bits of A, or of B when A is zero.
Mod 2^k the Fibonacci numbers repeat with period 3·2^(k-1), so 19 low bits of F(m) give m below 196,608 once m mod 12 is known.
When A and B are both non-zero their three low bits give m mod 12.
When one of them is zero there are up to three candidates, and a table addressed by slices of the non-zero word says which one.
The 14 remaining bits of the index come from two 2,048-entry tables, a 7-bit subtraction and a 7-bit multiplication.

**Check, 6,824 LUTs.** F(i-1), F(i) and F(i+1) are computed from the index with the same two tables and three multipliers.
The y term is on only if A equals s(F(i)) and B equals s(F(i-1)) bit for bit and i <= N-3. Its word is s(F(i+1)).
The points (0,0) and (0,1) are separate terms.

The multipliers are radix-4 Booth with one LUT per partial-product bit and 6:3 counters. One LUT per output joins the two halves.

## The proof

`proof/verify.py NAME ORIGINAL.aig NETLIST.blif`

The original:

- `sop` multiplies the original AIG out into a sum of products. This is exact: an AND node is a product of its fanins, a complemented AND is a sum of the complemented fanins.
  Each output of these three circuits, or its complement, comes out as about 37,000 products. Every product reads only x or only (A,B).
  The products over (A,B) are single input points, except one per circuit that covers two points. They are the table Y.
- All 131,072 values of x are simulated at an (A,B) outside that table. That is the table X.

The netlist:

1. Every output LUT is a function of fanins that depend only on x, OR a function of fanins that depend only on (A,B). So the netlist output is X'(x) OR Y'(A,B) too.
2. All 131,072 values of x at the same (A,B) give X. So X' = X.
3. The 18 wires that carry the index from the index logic to the check logic are cut open. With x fixed outside the table X, each of their 262,144 values is taken in turn.
   The check logic that depends only on those wires is then constant, and what is left of each output is a function of A and B alone. It is multiplied out. Every product must be a point of Y with that output bit set.
   The netlist drives the 18 wires from (A,B), so whatever it does is one of the enumerated cases: Y' is on only where Y is on.
4. At every point of Y the netlist gives the word of Y. So Y' = Y.

`blif2aig.py` turns the LUT netlist into AND and OR gates for step 3. Each LUT that depends on A or B is written twice, as an irredundant cover of its function and as one of its complement, and each cover is checked against the LUT's truth table.

Output for sixteen:

```
sixteen: original = ( X(x) OR Y(A,B) ); 950216 x products, 919725 y products (1 not a single point), 37334 table points
   the Fibonacci rule (N = 100000, n = 50) gives the same two tables: True
   netlist: 13092 LUTs
1. output LUTs of the form p(x side) OR q(y side): 50 of 50, 0 constant
2. all 131072 x patterns equal the original: True
3. cut values enumerated: 262144; products checked: 14334961 (largest sum 2, 262144 with free bits); failures: 0
4. table word at the table points: 37334 of 37334 equal
RESULT: equivalent to the original
```

## Run it

```
cd proof
./run.sh /path/to/EPFLfull/MtM
```

It needs a C compiler and Python 3. The three circuits take about nine minutes on one core of an Apple M1.

## Files

| | |
| --- | --- |
| `sixteen.blif`, `twenty.blif`, `twentythree.blif` | the netlists. Inputs and outputs have the names and order of the EPFL files, `in0` .. and `ot0` .. . The index wires are named `cut_t0` .. `cut_t13`, `cut_r0` .. `cut_r3`. |
| `proof/sop.c` | sum of products of every output of an AIG |
| `proof/xsim.c` | all values of inputs 0..16, the other inputs at 1 |
| `proof/psim.c` | simulation of a list of input patterns |
| `proof/blif2aig.py` | LUT netlist to AND/OR gates through exact covers |
| `proof/cutprove.c` | step 3 |
| `proof/verify.py`, `proof/run.sh` | the whole proof |
