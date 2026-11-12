#!/bin/sh
# Proves udiv equal to the Verilog operators / and % for every a and every b > 0, and its b = 0 outputs,
# with Yosys's SAT solver.  usage: prove.sh [max width, default 10]
set -eu
MAX=${1:-10}
DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
T=$(mktemp -d)
for W in $(seq 1 "$MAX"); do
  cat > "$T/m.v" <<V
module miter(input [$W-1:0] a, input [$W-1:0] b, output ok);
  wire [$W-1:0] q, r;
  udiv #(.WIDTH($W)) u(.a(a), .b(b), .q(q), .r(r));
  assign ok = (b == 0) ? (q == {$W{1'b1}} && r == a) : (q == a / b && r == a % b);
endmodule
V
  yosys -q -p "read_verilog $DIR/udiv.v $T/m.v; hierarchy -top miter; proc; flatten; opt; sat -prove ok 1 -verify" >/dev/null
  echo "WIDTH=$W proved"
done
rm -rf "$T"
