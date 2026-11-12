# CRC-32 modules for the taxi Ethernet MACs

Built against [fpganinja/taxi](https://github.com/fpganinja/taxi) `cc70b27`. Each module computes the same function as the `taxi_lfsr` instance it replaces
(`LFSR_W 32`, `LFSR_POLY 32'h4c11db7`, `LFSR_GALOIS 1`, `LFSR_FEED_FORWARD 0`, `REVERSE 1`, `DATA_OUT_EN 0`).

| Module | `taxi_lfsr` configuration | Used in | LUT-6 | Levels | Yosys `synth_xilinx`, same equations |
| --- | --- | --- | --- | --- | --- |
| `crc32_d8` | `DATA_W 8` | gmii rx/tx, basex rx_8/tx_8 | 40 | 3 | 122 |
| `crc32_d16` | `DATA_W 16` | basex rx_16 | 54 | 3 | 232 |
| `crc32_d32` | `DATA_W 32` | xgmii rx_32, baser rx_32 | 97 | 3 | 466 |
| `crc32_d64` | `DATA_W 64` | xgmii rx_64, baser rx_64 | 150 | 3 | 740 |
| `crc32_tx_d40` | `DATA_W 16+24`, `STATE_SHIFT_POST -24` | basex tx_16 | 41 | 2 | 114 |
| `crc32_tx_d56` | `DATA_W 32+24`, `STATE_SHIFT_POST -24` | xgmii tx_32, baser tx_32 | 75 | 2 | 230 |
| `crc32_tx_d88` | `DATA_W 64+24`, `STATE_SHIFT_POST -24` | xgmii tx_64, baser tx_64 | 121 | 3 | 500 |

Two files per module, same network: `NAME.v` (XOR assigns, one kept wire per LUT) and `NAME_lut6.v` (Xilinx LUT1..LUT6 primitives, module `NAME_lut6`).

Ports follow `taxi_lfsr`: `data_in`, `state_in`, `state_out`. The transmit modules have no `state_in`: those instances tie it to `'0`.

```systemverilog
crc32_d64 eth_crc (
    .data_in(xgmii_start_swap_reg ? {xgmii_rxd_masked[63:32], 32'd0} : xgmii_rxd_masked),
    .state_in(crc_state_reg),
    .state_out(crc_state)
);

crc32_tx_d88 eth_crc (
    .data_in(crc_data_reg),
    .state_out(crc_state)
);
```

## Byte-enabled

| Module | Bus | LUT-6 | Levels |
| --- | --- | --- | --- |
| `crc32_be_d64` | 8 bytes | 348 | 13 |
| `crc32_be_d32` | 4 bytes | 206 | 10 |

Ports: `data_in`, `state_in`, `empty`, `state_out`. `empty` is the number of bytes at the top of the word outside the frame.
`state_out` is the register after the first `W/8 - empty` bytes: that many chained `taxi_lfsr` `DATA_W 8` steps. Bytes past the valid ones must be zero.

One network computes the register after the whole word. Each zero byte at the end advances the register by a fixed linear map, so the register after the valid bytes is the inverse of that map applied `empty` times: one conditional stage per bit of `empty`.

## Check

`sim/eq_NAME.sv` instantiates `taxi_lfsr`, `NAME` and `NAME_lut6` side by side on 200,000 random inputs. `sim/lut_models.v` holds behavioural LUT1..LUT6.

```sh
verilator --binary --timing -Wno-fatal --top-module eq taxi_lfsr.sv sim/lut_models.v crc32_d64.v crc32_d64_lut6.v sim/eq_crc32_d64.sv
```

The top module is `eq` for the fixed-width modules and `eqbe` for the byte-enabled ones. All nine print `R 0`, Verilator 5.055.
Each fixed-width network is also checked as linear forms over GF(2) against the matrix read out of `taxi_lfsr` one input bit at a time.

Generator: [`../linear_compiler.py`](../) and [`../crc_gen.py`](../).
