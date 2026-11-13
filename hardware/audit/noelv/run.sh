#!/bin/sh
# Assembles a program of this folder and runs it on ./tb_core (built by build.sh in the current directory).
# usage: run.sh PROGRAM.S [CFG] [WAITS] [-DNAME=VALUE ...]
#   CFG    NOEL-V configuration: 1 = GP dual issue (default), 0 = HP, 6 = GP-lite
#   WAITS  wait states the memory inserts in every bus transfer (default 0)
# Needs llvm-mc and llvm-objcopy with the RISC-V target on PATH (or in $LLVM), a C preprocessor and Python 3.
# Prints "result ... flags ..." from the three doublewords the program stores.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
SRC=$1
CFG=${2:-1}
WAITS=${3:-0}
[ $# -ge 3 ] && shift 3 || shift $#
MC=${LLVM:+$LLVM/}llvm-mc
OBJCOPY=${LLVM:+$LLVM/}llvm-objcopy
cc -E -P -x assembler-with-cpp "$@" "$SRC" > prog.s
$MC -triple=riscv64 -mattr=+m,+a,+f,+d,+zicsr -filetype=obj -o prog.o prog.s
$OBJCOPY -O binary -j .text prog.o prog.bin
python3 "$HERE/bin2hex.py" prog.bin prog.hex
./tb_core -gprogfile=prog.hex -gcfg=$CFG -gwaits=$WAITS --ieee-asserts=disable 2> /dev/null | grep '^[WT] ' > prog.out
python3 "$HERE/report.py" prog.out
