# usage: python3 mkrand.py SEED N OUT [BITS]   -> N uniformly random integers as ":HEX" lines (operand B)
# BITS (default 64): with BITS below 64 every integer has exactly that many bits, the top one set.
import random
import sys

rng = random.Random(int(sys.argv[1]))
bits = int(sys.argv[4]) if len(sys.argv) > 4 else 64
with open(sys.argv[3], "w") as f:
    for _ in range(int(sys.argv[2])):
        v = rng.getrandbits(bits)
        if bits < 64:
            v |= 1 << (bits - 1)
        f.write(":%016x\n" % v)
print(sys.argv[3], sys.argv[2], "integers of", bits, "bits")
