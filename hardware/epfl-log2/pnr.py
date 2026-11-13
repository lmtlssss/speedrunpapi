#!/usr/bin/env python3
"""Place and route a log2 netlist on a Lattice ECP5-85F with Yosys and nextpnr.

usage: python3 pnr.py NAME NETLIST.blif [seed ...]

The netlist is put between two 32-bit register banks. Yosys maps it to the device's four-input LUTs and
wide-function multiplexers with one mapping pass (`strash; dretime; if`), nextpnr places and routes it,
and the script prints the logic cell count and the register-to-register clock period for each seed.
Needs `yosys` and `nextpnr-ecp5` on the path. Works for any BLIF with 32 inputs and 32 outputs; ports are
taken in the order of the `.inputs` and `.outputs` lines.
"""
import json
import os
import re
import subprocess
import sys


def ports(path, key):
    out, on = [], False
    for line in open(path):
        t = line.strip()
        if t.startswith("." + key):
            on, t = True, t[len(key) + 1:]
        elif on and (t.startswith(".") or not t):
            break
        elif not on:
            continue
        cont = t.endswith("\\")
        out += t.rstrip("\\").split()
        if not cont:
            break
    return out


def main():
    name, blif = sys.argv[1], os.path.abspath(sys.argv[2])
    seeds = [int(s) for s in sys.argv[3:]] or [1, 2, 3]
    os.makedirs(name, exist_ok=True)
    ins, outs = ports(blif, "inputs"), ports(blif, "outputs")
    assert len(ins) == 32 and len(outs) == 32, (len(ins), len(outs))
    conn = ", ".join([".\\%s (a[%d])" % (p, i) for i, p in enumerate(ins)] +
                     [".\\%s (r[%d])" % (p, i) for i, p in enumerate(outs)])
    with open(name + "/wrap.v", "w") as f:
        f.write("module top(input clk, input [31:0] ai, output reg [31:0] ro);\n"
                "  reg [31:0] a; wire [31:0] r;\n"
                "  always @(posedge clk) begin a <= ai; ro <= r; end\n"
                "  core c(%s);\nendmodule\n" % conn)
    with open(name + "/map.abc", "w") as f:
        f.write("strash; dretime; if\n")
    script = ("read_blif %s; rename -top core; read_verilog %s/wrap.v; "
              "synth_ecp5 -top top -run begin:map_luts; abc -lut 4:7 -script %s/map.abc; clean; "
              "techmap -map +/lattice/cells_map_trellis.v; opt_lut_ins -tech lattice; clean; autoname; "
              "hierarchy -check; blackbox =A:whitebox; write_json %s/top.json"
              % (blif, name, os.path.abspath(name), name))
    subprocess.run(["yosys", "-q", "-p", script], check=True)
    for seed in seeds:
        p = subprocess.run(["nextpnr-ecp5", "--85k", "--package", "CABGA756", "--json", name + "/top.json",
                            "--freq", "20", "--seed", str(seed), "--timing-allow-fail"],
                           capture_output=True, text=True)
        log = p.stderr + p.stdout
        mhz = re.findall(r"Max frequency for clock\s+'\S+':\s+([\d.]+) MHz", log)
        cells = re.search(r"TRELLIS_COMB:\s+(\d+)/", log)
        print(json.dumps({"netlist": name, "seed": seed, "logic_cells": int(cells.group(1)) if cells else None,
                          "period_ns": round(1000 / float(mhz[-1]), 2) if mhz else None}))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
