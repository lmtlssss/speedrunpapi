#!/bin/sh
# Microwatt's fpu.vhdl at its own port, beside exact arithmetic. Needs GHDL and Python 3.
# MICROWATT is the directory of a checkout of antonblanchard/microwatt (f341bed here).
#
#   MICROWATT=DIR ./run.sh build [FPU_SOURCE] [BINARY]    the testbench with DIR/fpu.vhdl, or with another file
#   MICROWATT=DIR ./run.sh enabled SEED N TAG [BINARY]    N operand sets per instruction under seven enable settings
#   MICROWATT=DIR ./run.sh idiv SEED N TAG [BINARY]       N operand pairs for each of the twelve integer divisions
#   MICROWATT=DIR ./run.sh one TAG BINARY NAME RN EN A:B:C ...   chosen operands (RN 0..3 or all, EN in hex)
#
# Each run writes TAG.vec, TAG.meta, TAG.out and TAG.report in the current directory.
HERE=$(cd "$(dirname "$0")" && pwd)
MW=${MICROWATT:?set MICROWATT to the checkout}
export MICROWATT
cmd=$1
shift
case "$cmd" in
  build)
    FPU=${1:-$MW/fpu.vhdl}
    BIN=${2:-tb_mw}
    mkdir -p work_$BIN
    OPT="--std=08 --workdir=work_$BIN"
    ghdl -a $OPT $MW/decode_types.vhdl $MW/utils.vhdl $MW/common.vhdl $MW/helpers.vhdl $MW/crhelpers.vhdl \
      $MW/insn_helpers.vhdl $MW/multiply.vhdl $FPU $HERE/tb_mw.vhd || exit 1
    ghdl -e $OPT -o $BIN tb_mw || exit 1
    echo "built $BIN"
    ;;
  enabled)
    BIN=${4:-tb_mw}
    python3 $HERE/mw_enabled.py gen $1 $2 $3 || exit 1
    ./$BIN -gvecfile=$3.vec -goutfile=$3.out > $3.simlog 2>&1
    python3 $HERE/mw_enabled.py check $3 4 > $3.report
    tail -n 12 $3.report
    ;;
  idiv)
    BIN=${4:-tb_mw}
    python3 $HERE/mw_idiv.py gen $1 $2 $3 || exit 1
    ./$BIN -gvecfile=$3.vec -goutfile=$3.out > $3.simlog 2>&1
    python3 $HERE/mw_idiv.py check $3 4 > $3.report
    tail -n 16 $3.report
    ;;
  one)
    TAG=$1
    BIN=$2
    shift 2
    python3 $HERE/mw_enabled.py one $TAG "$@" || exit 1
    ./$BIN -gvecfile=$TAG.vec -goutfile=$TAG.out > $TAG.simlog 2>&1
    python3 $HERE/mw_enabled.py check $TAG 8 > $TAG.report
    cat $TAG.report
    ;;
  *)
    echo "usage: MICROWATT=DIR $0 build|enabled|idiv|one ..."
    exit 2
    ;;
esac
