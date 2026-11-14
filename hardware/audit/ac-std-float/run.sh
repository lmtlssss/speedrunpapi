#!/bin/sh
# usage: AC_TYPES=/path/to/ac_types ./run.sh repro | small "FORMATS" "OPS" | host [SEED N] | patched
#
#   repro     the three findings on the library as it is: a few lines each
#   small     every operand of each small format through each operation, in the four rounding modes,
#             checked by acref.py; one summary line per run.   example: ./run.sh small "8.3 10.4" "add sub"
#   host      binary32 and binary64 in round to nearest even beside the processor's own arithmetic
#   patched   applies ac_std_float.patch to a copy of the header, then runs repro and three small runs with it
#
# AC_TYPES is a checkout of https://github.com/hlslibs/ac_types. Needs a C++17 compiler (CXX, default c++)
# and Python 3. Everything is built into ./build beside this script.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -z "$AC_TYPES" ] || [ ! -f "$AC_TYPES/include/ac_std_float.h" ]; then
  echo "set AC_TYPES to a checkout of hlslibs/ac_types" >&2
  exit 2
fi
CXX=${CXX:-c++}
B="$HERE/build"
mkdir -p "$B"

build() {   # build FIRST_INCLUDE_DIR SUFFIX
  for p in actb acfma acadd aczero achost acbuiltin; do
    "$CXX" -std=c++17 -O2 -w -I "$1" -I "$AC_TYPES/include" "$HERE/$p.cpp" -o "$B/$p$2"
  done
  # the same source once more with the library's C-library mode for binary32 and binary64
  "$CXX" -std=c++17 -O2 -w -DAC_IEEE_FLOAT_USE_BUILTIN -I "$1" -I "$AC_TYPES/include" "$HERE/acbuiltin.cpp" -o "$B/acbuiltin_c$2"
}

sweep() {   # sweep SUFFIX "FORMATS" "OPS"
  for fmt in $2; do
    for op in $3; do
      for rnd in conv zero inf odd; do
        "$B/actb$1" "$op" "$fmt" "$rnd" > "$B/results.txt"
        python3 "$HERE/acref.py" check "$op" "$fmt" "$rnd" "$B/results.txt" 2
      done
    done
  done
}

case "$1" in
  repro)
    build "$AC_TYPES/include" ""
    "$B/acfma"
    "$B/acadd"
    "$B/aczero"
    "$B/acbuiltin"
    "$B/acbuiltin_c"
    ;;
  small)
    build "$AC_TYPES/include" ""
    sweep "" "${2:-8.3}" "${3:-add sub mult div sqrt}"
    ;;
  host)
    build "$AC_TYPES/include" ""
    "$B/achost" "${2:-1}" "${3:-1000000}"
    ;;
  patched)
    mkdir -p "$B/patched"
    cp "$AC_TYPES/include/ac_std_float.h" "$B/patched/ac_std_float.h"
    patch -s -p2 -d "$B/patched" < "$HERE/ac_std_float.patch"
    build "$B/patched" "_patched"
    "$B/acfma_patched"
    "$B/acadd_patched"
    "$B/aczero_patched"
    "$B/acbuiltin_patched"
    "$B/acbuiltin_c_patched"
    sweep "_patched" "6.3" "fma"
    sweep "_patched" "10.4" "add sub"
    sweep "_patched" "10.4" "ceil floor trunc round"
    ;;
  *)
    sed -n '2,10p' "$0"
    exit 2
    ;;
esac
