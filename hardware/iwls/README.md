# IWLS contest functions ex280 to ex294

The IWLS 2026 programming contest gave 100 functions as truth tables and asked for AND-inverter graphs.
Twelve teams entered, and every circuit they submitted is public in [alanminko/iwls2026-ls-contest](https://github.com/alanminko/iwls2026-ls-contest).
The functions come without a description.

This folder holds the rule behind fifteen of them, `ex280` to `ex294`, and one circuit per function built from its rule.
For `ex290` to `ex294` the circuit here is 5 to 12 times smaller than the smallest in the contest.

| Function | Inputs | Smallest in the contest, AND nodes | Here, AND nodes | Levels here |
| --- | --- | --- | --- | --- |
| `ex290` | 12 | 2,868 | 519 | 14 |
| `ex291` | 13 | 4,478 | 564 | 15 |
| `ex292` | 14 | 5,557 | 605 | 14 |
| `ex293` | 15 | 6,849 | 640 | 15 |
| `ex294` | 16 | 8,383 | 683 | 15 |

For `ex280` to `ex289` the contest already has circuits of this size.

| Function | Inputs | Smallest in the contest, AND nodes | Here, AND nodes | Levels here |
| --- | --- | --- | --- | --- |
| `ex280` | 12 | 109 | 106 | 26 |
| `ex281` | 13 | 118 | 117 | 28 |
| `ex282` | 14 | 126 | 126 | 30 |
| `ex283` | 15 | 144 | 137 | 32 |
| `ex284` | 16 | 149 | 146 | 34 |
| `ex285` | 12 | 154 | 170 | 14 |
| `ex286` | 13 | 173 | 188 | 14 |
| `ex287` | 14 | 194 | 212 | 14 |
| `ex288` | 15 | 232 | 239 | 14 |
| `ex289` | 16 | 244 | 272 | 14 |

"Smallest in the contest" is the lowest AND count over all teams in `results/pareto_tables/` of the contest repository.
The counts here are `and` and `lev` from ABC `print_stats`.

## What the functions compute

Each function has n inputs and n outputs. x is the input word, bit 0 is the first input, and indices run mod n.

```
ex280 - ex284     n = 12 ... 16

g_k   = x_0 ^ x_1 ^ ... ^ x_k
y_k   = g_k ? x_{n-1-k} : x_{k+1}
h_k   = y_0 ^ ... ^ y_{k-1}               h_0 = 0
out_k = majority(h_k, y_k, y_{k+2})
```

```
ex285 - ex289     n = 12 ... 16           a = x[3:0], t = x[n-1:n-4], s = a ^ t

b = x
every pair (b[2j], b[2j+1]) is sorted: the larger bit goes to 2j+1 when s_0 = 0, to 2j when s_0 = 1
for k = 1, 2, 3 with D = 2^k:
    for every i with bit k of i clear and i + D < n:
        exchange b[i] and b[i+D] when b[i^1], read before the stage, equals s_k
out = b
```

The output has as many ones as the input.

```
ex290 - ex294     n = 12 ... 16           a = x[3:0], t = x[n-1:n-4]

L(s)  = bits n ... 2n-1 of ({x, x} << s)  x rotated left by s; zeros enter once s > n
R(s)  = bits 0 ... n-1  of ({x, x} >> s)  x rotated right by s; zeros enter once s > n
g     = L(a ^ t) | (L(a) ^ R(t))
out_i = g_i ^ (~g_{i+1} & g_{i+2})
```

## Check

[`rules.py`](rules.py) holds the three rules as Python and compares them with the contest truth tables on every input.

```
python3 rules.py <folder with ex280.truth ... ex294.truth>
```

Each circuit against its truth table, in ABC:

```
abc -c "read_aiger ex294.aig; print_stats; &get; &cec -t ex294.truth"
```

## Files

`ex280.aig` to `ex294.aig` are binary AIGER, inputs and outputs in the order of the truth tables.
The truth tables are `benchmarks/truth/` in the contest repository.
