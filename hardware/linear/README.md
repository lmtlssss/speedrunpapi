# Linear-map compiler

Builds `y = M x` over GF(2) as a network of XOR LUTs, with a proof.
`crc_gen.py` builds the CRC of a wide bus for any number of valid bytes.

Uses: CRC, scramblers, encoders and syndrome logic of block codes, constant multipliers in GF(2^m).

## Method

A set of signals that occurs in several rows of `M` is built once.
The set starts as the most frequent pair and takes one signal at a time while `(size - 1) * (rows containing it)` grows. It becomes one LUT and replaces itself in those rows.
When no set occurs twice, each row is closed with a tree, earliest signals first.
`--depth` limits the LUT levels: shared sets are then taken from signals below a level cap.

Wide bus, variable length. One network computes the register after the whole bus, `F(s, d)`. A zero byte advances the register by a fixed map `A^8`, so with `e` empty bytes at the end the register after the valid bytes is `A^(-8e) F(s, d)`. `A^(-8e)` is one conditional stage per bit of `e`: `x' = x ^ (e_j & (U_j + I) x)`, with `U_j = A^(-8 * 2^j)`.

## Results

CRC-32, polynomial `0x04C11DB7`, register after one bus word. LUT-6 counts.
Yosys: 0.70 `synth_xilinx` on the XOR equations. ISE: Xilinx ISE 14.6 on the XOR equations, Virtex-7, as printed in Závodník, Kekely, Puš, "CRC Based Hashing in FPGA Using DSP Blocks" (CESNET), Table I.

| Bus | Yosys | ISE | This compiler | `--depth` at the minimum |
| --- | --- | --- | --- | --- |
| 64 bits | 378 | | 171, 5 levels | 181, 3 levels |
| 128 bits | 687 | 347 | 270, 5 levels | 265, 4 levels |
| 256 bits | 1223 | 711 | 439, 5 levels | 442, 4 levels |
| 512 bits | 2344 | 1314 | 731, 5 levels | 803, 4 levels |
| 1024 bits | 4662 | 2433 | 1280, 6 levels | 1296, 5 levels |

CRC-32 of a bus with any number of valid bytes (`crc_gen.py`). The bytes past the valid ones arrive as zero.
Reference: Zhang et al., Electronics 13(22):4399, 2024, Table 2, their design on Virtex UltraScale+ with Vivado 2020.2; that module contains its data shifters.

| Bus | Zhang et al. | `crc_gen.py` | File |
| --- | --- | --- | --- |
| 8 bytes | 510 LUT | 390 LUT-6, 15 levels | `crc32/crc32_b8.v` |
| 16 bytes | 818 | 592, 19 levels | |
| 32 bytes | 1550 | 865, 23 levels | |
| 64 bytes | 3519 | 1256, 27 levels | `crc32/crc32_b64.v` |
| 128 bytes | 5981 | 1907, 32 levels | |

One CRC per length followed by a select, 8-byte bus, under Yosys: 1679 LUT-6.

Reed-Solomon (544,514) over GF(2^10), encoder register update for 4 symbols per clock, 300 outputs of 340 inputs: Yosys 2576 LUT-6, this compiler 971 (`rs/`).

Lattice ECP5, 64-bit bus, placed and routed (Yosys `synth_ecp5` + nextpnr-ecp5, registers on both sides, best of 3 seeds): the XOR equations take 531 cells and 5.64 ns; the LUT-4 build takes 227 cells and 5.70 ns.

The CRC recurrence equals zlib `crc32` when each byte enters least significant bit first, the register starts at all ones, and the result is bit-reversed and inverted.

## Run

```sh
python3 linear_compiler.py --data 512 --depth 4 --out out/
python3 independent_linear_checker.py --netlist out/crc.blif --derivation out/crc.json
python3 crc_gen.py --bytes 64 --out out/            # add --family xilinx or --k 4 --family ecp5 for LUT instances
python3 independent_crc_checker.py --netlist out/crc.blif --derivation out/crc.json
python3 rs_encoder.py 4 > rs.rows
python3 linear_compiler.py --matrix rs.rows --inputs 340 --out out/
python3 independent_linear_checker.py --netlist out/linear.blif --derivation out/linear.json
python3 test_linear.py
```

`--matrix` takes any GF(2) matrix: one row per line as a hex mask over the inputs.
The plain Verilog output is one expression per LUT. Synthesis tools rebuild XOR expressions; the `--family` output instantiates the LUTs and keeps the network (390 stays 390 through `synth_xilinx`).

## Proof

`independent_linear_checker.py` and `independent_crc_checker.py` share no code with the compiler.
Every LUT must be the parity of a subset of its inputs once constant inputs are fixed. Each wire then carries one GF(2) linear form, held as a bit mask over the inputs.
The masks of the outputs are compared with the claim: the rows of the matrix, or the masks obtained by running the bit-serial CRC recurrence on symbolic inputs. For the variable-length module this is done for every number of valid bytes.
Equal masks are equal functions on every input.

`test_linear.py`: 60 random maps, CRC-16 and CRC-32 networks, and 160 netlists with one minterm removed, all rejected.
The emitted modules are simulated against a software CRC on random states, lengths and data.

## Paid evaluation

One block of yours, in your flow: 2,500 USD, fixed.

You send the polynomial or matrix, the bus width, the FPGA family and your reference RTL. You receive the network as Verilog, the proof files with the independent checker, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on LUT count or logic depth.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

Python 3.9+, standard library only. Licence: see `LICENSE.md` at the repository root.
