#!/bin/sh
# usage: ./run.sh /path/to/EPFLfull/MtM
# Builds the four C tools and proves the three netlists in the parent directory equivalent to the
# EPFL originals (EPFL_complete.tar.gz, Zenodo record 2572934). Needs a C compiler and Python 3.
set -e
cd "$(dirname "$0")"
for t in sop xsim psim cutprove; do cc -O3 -o $t $t.c; done
ulimit -s unlimited 2>/dev/null || ulimit -s 65520 2>/dev/null || true
for c in sixteen twenty twentythree; do
  python3 verify.py $c "$1/$c/aiger/$c.aig" ../$c.blif
done
