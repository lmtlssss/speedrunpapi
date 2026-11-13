#!/bin/sh
# Analyses the NOEL-V core of a GRLIB release with GHDL, with the options GRLIB's own GHDL flow uses, and
# elaborates the testbench of this folder into ./tb_core in the current directory.
# usage: build.sh /path/to/grlib-gpl-2026.3-b4301 [patched nanofpunv.vhd]
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
python3 "$HERE/mklist.py" "$1/lib" $2 > files.txt
mkdir -p work
OPT="--std=93c -fexplicit --ieee=synopsys --mb-comments --workdir=work -Pwork"
while read lib f; do
  ghdl -a $OPT --work=$lib "$f" 2> ghdl.log || { echo "failed: $f"; grep -v warning ghdl.log | head; exit 1; }
done < files.txt
ghdl -a $OPT --work=work "$HERE/tb_core.vhd"
ghdl -e $OPT --warn-no-binding --warn-no-hide --work=work -o tb_core tb_core 2> ghdl.log
echo "built ./tb_core from $(wc -l < files.txt) files"
