#!/bin/sh
# Proves udivf equal to the Verilog operators / and % for every a and every b > 0, and its b = 0 outputs,
# with Yosys's SAT solver, at widths 8, 10 and 12 (folds of 2, 3 and 4 bits).
set -eu
DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
T=$(mktemp -d)
for WF in "8 2" "10 3" "12 4"; do
  W=${WF% *}; F=${WF#* }
  python3 "$DIR/udivf_gen.py" "$W" "$F" > "$T/u.v"
  cat > "$T/m.v" <<V
module miter(input [$W-1:0] a, input [$W-1:0] b, output ok);
  wire [$W-1:0] q, r;
  udivf$W u(.a(a), .b(b), .q(q), .r(r));
  assign ok = (b == 0) ? (q == {$W{1'b1}} && r == a) : (q == a / b && r == a % b);
endmodule
V
  yosys -q -p "read_verilog $T/u.v $T/m.v; hierarchy -top miter; proc; flatten; memory; opt; sat -prove ok 1 -verify" >/dev/null
  echo "WIDTH=$W fold=$F proved"
done
rm -rf "$T"
