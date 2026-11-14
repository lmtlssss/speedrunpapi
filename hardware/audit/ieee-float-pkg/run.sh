#!/bin/sh
# The plain calls and N vectors per operation, format and style, against the float package the simulator ships
# and against the patched body.
#
#   sh run.sh ghdl /path/to/ieee [N]
#   sh run.sh nvc  /path/to/ieee [N]
#
# /path/to/ieee holds float_generic_pkg.vhdl, float_generic_pkg-body.vhdl and float_pkg.vhdl: the directory
# "ieee" of https://opensource.ieee.org/vasg/Packages, or lib/ghdl/src/ieee2008 of a GHDL installation.
# The patched body goes into a library of its own, "patched", beside the declaration it belongs to.
SIM=$1
IEEE=$2
N=${3:-2500}
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p build-$SIM && cd build-$SIM || exit 1

cp "$IEEE/float_generic_pkg-body.vhdl" . || exit 1
patch -s float_generic_pkg-body.vhdl "$HERE/float_generic_pkg-body.patch" || exit 1
sed 's/is new IEEE.float_generic_pkg/is new work.float_generic_pkg/' "$IEEE/float_pkg.vhdl" > float_pkg.vhdl
for tb in plain tb_float_pkg; do
  sed -e 's/use ieee.float_pkg.all;/library patched; use patched.float_pkg.all;/' \
    -e "s/entity $tb is/entity ${tb}_patched is/" -e "s/of $tb is/of ${tb}_patched is/" \
    "$HERE/$tb.vhd" > ${tb}_patched.vhd
done

if [ "$SIM" = ghdl ]; then
  ghdl -a --std=08 --work=patched "$IEEE/float_generic_pkg.vhdl" float_generic_pkg-body.vhdl float_pkg.vhdl || exit 1
  ghdl -a --std=08 "$HERE/plain.vhd" plain_patched.vhd "$HERE/tb_float_pkg.vhd" tb_float_pkg_patched.vhd || exit 1
  for top in plain plain_patched tb_float_pkg tb_float_pkg_patched; do
    ghdl -e --std=08 $top || exit 1
  done
  sim() { top=$1; shift; ghdl -r --std=08 $top "$@"; }
else
  nvc --std=2008 --work=patched -a "$IEEE/float_generic_pkg.vhdl" float_generic_pkg-body.vhdl float_pkg.vhdl || exit 1
  nvc --std=2008 -L . -a "$HERE/plain.vhd" plain_patched.vhd "$HERE/tb_float_pkg.vhd" tb_float_pkg_patched.vhd || exit 1
  sim() { top=$1; shift; nvc --std=2008 -L . -e "$@" $top -r; }
fi

echo "== plain calls, the package as shipped"
sim plain 2>&1 | cut -c1-120
echo "== plain calls, patched"
sim plain_patched 2>&1 | cut -c1-120

python3 "$HERE/exact.py" gen 2026 $N 5,10 8,23 11,52 15,112 > vectors.txt
if [ "$SIM" = ghdl ]; then
  python3 "$HERE/exact.py" run vectors.txt shipped.txt -- ghdl -r --std=08 tb_float_pkg "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}"
  python3 "$HERE/exact.py" run vectors.txt patched.txt -- ghdl -r --std=08 tb_float_pkg_patched "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}"
else
  python3 "$HERE/exact.py" run vectors.txt shipped.txt -- nvc --std=2008 -L . -e "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}" tb_float_pkg -r
  python3 "$HERE/exact.py" run vectors.txt patched.txt -- nvc --std=2008 -L . -e "-gvecfile={vec}" "-goutfile={out}" "-gskip={skip}" tb_float_pkg_patched -r
fi
echo "== the package as shipped: wrong of compared, by operation and rounding style"
python3 "$HERE/exact.py" check vectors.txt shipped.txt | sed -n '/^format/,$p'
echo "== patched"
python3 "$HERE/exact.py" check vectors.txt patched.txt | tail -n 1
