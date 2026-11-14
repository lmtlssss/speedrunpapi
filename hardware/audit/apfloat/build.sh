#!/bin/sh
# build.sh                  the harness against the installed LLVM (Homebrew), as released: apf
# build.sh trunk DIR [OUT] [APFLOAT_CPP]
#                           the harness with APFloat.cpp and the headers of the LLVM checkout in DIR,
#                           assertions on; the generated llvm/Config headers and the rest of LLVMSupport
#                           come from the installed library. OUT is the binary (apf_trunk); APFLOAT_CPP
#                           replaces DIR's llvm/lib/Support/APFloat.cpp (a patched copy).
# build.sh trunk-noassert DIR [OUT] [APFLOAT_CPP]     the same with assertions off
set -eu
cd "$(dirname "$0")"
LC=/opt/homebrew/opt/llvm/bin/llvm-config
INC="$("$LC" --includedir)"
LIBS="$("$LC" --ldflags) $("$LC" --libs support) $("$LC" --system-libs)"
case "${1:-}" in
trunk | trunk-noassert)
  T="$2"
  OUT="${3:-apf_trunk}"
  SRC="${4:-$T/llvm/lib/Support/APFloat.cpp}"
  if [ "$1" = trunk ]; then A="-UNDEBUG"; else A="-DNDEBUG"; fi
  mkdir -p obj
  c++ -std=c++17 -O1 -g -w $A -I "$T/libc" -I "$T/llvm/include" -I "$INC" -I "$T/llvm/lib/Support" -c "$SRC" -o "obj/$OUT.APFloat.o"
  c++ -std=c++17 -O1 -g -w $A -DHAVE_E5M3FNU -I "$T/llvm/include" -I "$INC" apf.cpp "obj/$OUT.APFloat.o" -o "$OUT" $LIBS
  ;;
*)
  c++ -std=c++17 -O2 -w -I "$INC" apf.cpp -o apf $LIBS
  ;;
esac
