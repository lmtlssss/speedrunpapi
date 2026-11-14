#!/bin/sh
# Every operand of a set of small index ranges through the fixed-point package the simulator ships and through
# the patched body.
#
#   sh run_fixed.sh ghdl /path/to/ieee
#   sh run_fixed.sh nvc  /path/to/ieee
#
# /path/to/ieee holds fixed_generic_pkg.vhdl, fixed_generic_pkg-body.vhdl and fixed_pkg.vhdl: the directory
# "ieee" of https://opensource.ieee.org/vasg/Packages, or lib/ghdl/src/ieee2008 of a GHDL installation.
SIM=$1
IEEE=$2
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p build-fixed-$SIM && cd build-fixed-$SIM || exit 1

cp "$IEEE/fixed_generic_pkg-body.vhdl" . || exit 1
patch -s fixed_generic_pkg-body.vhdl "$HERE/fixed_generic_pkg-body.patch" || exit 1
sed 's/is new IEEE.fixed_generic_pkg/is new work.fixed_generic_pkg/' "$IEEE/fixed_pkg.vhdl" > fixed_pkg.vhdl
sed -e 's/use ieee.fixed_pkg.all;/library patched; use patched.fixed_pkg.all;/' \
  -e 's/entity tb_fixed is/entity tb_fixed_patched is/' -e 's/of tb_fixed is/of tb_fixed_patched is/' \
  "$HERE/tb_fixed.vhd" > tb_fixed_patched.vhd

python3 "$HERE/fixed_exact.py" gen > vectors.txt
if [ "$SIM" = ghdl ]; then
  ghdl -a --std=08 --work=patched "$IEEE/fixed_generic_pkg.vhdl" fixed_generic_pkg-body.vhdl fixed_pkg.vhdl || exit 1
  ghdl -a --std=08 "$HERE/tb_fixed.vhd" tb_fixed_patched.vhd || exit 1
  ghdl -e --std=08 tb_fixed || exit 1
  ghdl -e --std=08 tb_fixed_patched || exit 1
  python3 "$HERE/exact.py" run vectors.txt shipped.txt -- ghdl -r --std=08 tb_fixed "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}"
  python3 "$HERE/exact.py" run vectors.txt patched.txt -- ghdl -r --std=08 tb_fixed_patched "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}"
else
  nvc --std=2008 --work=patched -a "$IEEE/fixed_generic_pkg.vhdl" fixed_generic_pkg-body.vhdl fixed_pkg.vhdl || exit 1
  nvc --std=2008 -L . -a "$HERE/tb_fixed.vhd" tb_fixed_patched.vhd || exit 1
  python3 "$HERE/exact.py" run vectors.txt shipped.txt -- nvc --std=2008 -L . -e "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}" tb_fixed -r
  python3 "$HERE/exact.py" run vectors.txt patched.txt -- nvc --std=2008 -L . -e "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}" tb_fixed_patched -r
fi
echo "== the package as shipped: wrong of compared"
python3 "$HERE/fixed_exact.py" check vectors.txt shipped.txt | grep -v "^  "
echo "== patched"
python3 "$HERE/fixed_exact.py" check vectors.txt patched.txt | tail -n 1
