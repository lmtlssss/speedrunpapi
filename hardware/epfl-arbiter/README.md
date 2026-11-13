# EPFL arbiter

`arbiter` is the round-robin arbiter of the [EPFL combinational benchmark suite](https://github.com/lsils/benchmarks): 256 inputs, 129 outputs, 11,839 AND nodes.
The suite keeps a list of the smallest known LUT-6 implementations.

| | LUT-6 | Levels |
| --- | --- | --- |
| Smallest published, `best_results/size/arbiter_size_2026.blif` | 259 | 93 |
| [`arbiter_size_2027.blif`](arbiter_size_2027.blif) | 256 | 65 |

The first row is the suite's table. The second is `nd` and `lev` from ABC `print_stats`.

## What the benchmark computes

The inputs are `priority[0..127]` and `req[0..127]`. A token starts at every set priority bit and travels upward. The first request it meets takes it and is granted. A token that leaves position 127 enters again at 0.

```
v[0]     = priority[0]
v[i]     = priority[i] | (v[i-1] & ~req[i-1])        the token that reaches i when nothing re-enters
w        = v[127] & ~req[127]                        the token that leaves the top
nr[i]    = ~(req[0] | ... | req[i-1])                no request below i

grant[i] = req[i] & (v[i] | (w & nr[i]))
anyGrant = req[0] | ... | req[127]
```

With one priority bit set, the first request at or above it gets the grant, wrapping around. With several set, each token finds its own request. With none set there is no grant, and `anyGrant` still reports the requests.

## The netlist

[`build.py`](build.py) writes it from these equations. Every one of the 129 outputs needs its own LUT, which leaves 127 for everything else.

- `v` and `nr` exist as wires at the even positions only: 63 LUTs each. A step of `v` over two positions has five inputs.
- A grant LUT at an even position reads `req`, `v`, `nr` and `w`. At an odd position it reads those of the position below and the three bits between: six inputs.
- `w` is one more step of the `v` chain, and `anyGrant` is the last step of the `nr` chain.

128 + 63 + 63 + 1 + 1 = 256.

## Check

ABC proves the netlist equal to the benchmark in under a second.

```
abc -c "cec -n <random_control/arbiter.aig of lsils/benchmarks> arbiter_size_2027.blif"
```

```
Networks are equivalent.
```

The same command runs on each change to this folder against `arbiter.aig` of lsils/benchmarks commit `82d8cc6` ([workflow](../../.github/workflows/epfl-arbiter.yml)).
