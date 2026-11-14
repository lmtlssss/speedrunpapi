#!/bin/sh
# build_ut.sh DIR NAME [TEST_CPP]
# LLVM's own APFloat unit tests with the googletest bundled in the LLVM checkout DIR, linked with the
# APFloat object that "build.sh trunk DIR NAME ..." made (obj/NAME.APFloat.o) and the installed
# LLVMSupport. TEST_CPP replaces DIR/llvm/unittests/ADT/APFloatTest.cpp (a patched copy).
# The test binary is ut_NAME.
set -eu
cd "$(dirname "$0")"
T="$1"
NAME="$2"
TEST="${3:-$T/llvm/unittests/ADT/APFloatTest.cpp}"
LC=/opt/homebrew/opt/llvm/bin/llvm-config
INC="$("$LC" --includedir)"
LIBS="$("$LC" --ldflags) $("$LC" --libs support) $("$LC" --system-libs)"
G="$T/third-party/unittest/googletest"
FLAGS="-std=c++17 -O1 -w -UNDEBUG -I $T/llvm/include -I $INC -I $G/include -I $G"
mkdir -p obj/ut
[ -f obj/ut/gtest-all.o ] || c++ $FLAGS -c "$G/src/gtest-all.cc" -o obj/ut/gtest-all.o
[ -f obj/ut/gtest_main.o ] || c++ $FLAGS -c "$G/src/gtest_main.cc" -o obj/ut/gtest_main.o
c++ $FLAGS -c "$TEST" -o "obj/ut/$NAME.APFloatTest.o"
c++ "obj/ut/$NAME.APFloatTest.o" obj/ut/gtest-all.o obj/ut/gtest_main.o "obj/$NAME.APFloat.o" -o "ut_$NAME" $LIBS
