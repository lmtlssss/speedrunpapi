#!/usr/bin/env python3
"""Write the DSLX wrappers that instantiate XLS's apfloat functions at small sizes, with flat ports.

usage: mkwrap.py OUT.x TOPS.txt

One function per (operation, format). TOPS.txt lists them: name, the widths of the inputs, the width of
the output, and what it is, for the testbench generator and the reference.
  add_4_3 8,8 8 add 4 3
"""
import sys

FORMATS = [(3, 2), (4, 3), (3, 4), (5, 2)]
WIDE = [(5, 6), (4, 7)]
out = ["import apfloat;", ""]
tops = []


def w(e, f):
    return 1 + e + f


def un(e, f, x):
    return "apfloat::unflatten<u32:%d, u32:%d>(%s)" % (e, f, x)


def fl(expr):
    return "apfloat::flatten(%s)" % expr


def fn(name, args, ret, body, what):
    out.append("pub fn %s(%s) -> uN[%d] {" % (name, ", ".join("%s: %s" % (n, t) for n, t, _ in args), ret))
    out.append("    " + body)
    out.append("}")
    out.append("")
    tops.append("%s %s %d %s" % (name, ",".join(str(wd) for _, _, wd in args), ret, what))


for e, f in FORMATS:
    W = w(e, f)
    T = "uN[%d]" % W
    P = "<u32:%d, u32:%d>" % (e, f)
    a, b, c = un(e, f, "a"), un(e, f, "b"), un(e, f, "c")
    two = [("a", T, W), ("b", T, W)]
    one = [("a", T, W)]
    fn("add_%d_%d" % (e, f), two, W, fl("apfloat::add%s(%s, %s)" % (P, a, b)), "add %d %d" % (e, f))
    fn("addlza_%d_%d" % (e, f), two, W, fl("apfloat::add<u32:%d, u32:%d, true>(%s, %s)" % (e, f, a, b)), "add %d %d" % (e, f))
    fn("sub_%d_%d" % (e, f), two, W, fl("apfloat::sub%s(%s, %s)" % (P, a, b)), "sub %d %d" % (e, f))
    fn("mul_%d_%d" % (e, f), two, W, fl("apfloat::mul%s(%s, %s)" % (P, a, b)), "mul %d %d" % (e, f))
    fn("fma_%d_%d" % (e, f), two + [("c", T, W)], W, fl("apfloat::fma%s(%s, %s, %s)" % (P, a, b, c)), "fma %d %d" % (e, f))
    for nm, call in (("ceil", "ceil_with_denorms"), ("ceildaz", "ceil_daz"), ("floor", "floor_with_denorms"),
                     ("floordaz", "floor_daz"), ("trunc", "trunc")):
        fn("%s_%d_%d" % (nm, e, f), one, W, fl("apfloat::%s%s(%s)" % (call, P, a)), "%s %d %d" % (nm, e, f))
    fn("round_%d_%d" % (e, f), one, W,
       fl("apfloat::round<u32:%d, u32:%d, apfloat::RoundStyle::TIES_TO_EVEN>(%s)" % (e, f, a)), "round %d %d" % (e, f))
    fn("rounda_%d_%d" % (e, f), one, W,
       fl("apfloat::round<u32:%d, u32:%d, apfloat::RoundStyle::TIES_TO_AWAY>(%s)" % (e, f, a)), "rounda %d %d" % (e, f))
    for nm, call in (("eq", "eq_2"), ("gt", "gt_2"), ("gte", "gte_2"), ("lte", "lte_2"), ("lt", "lt_2")):
        fn("%s_%d_%d" % (nm, e, f), two, 1, "apfloat::%s%s(%s, %s) as uN[1]" % (call, P, a, b), "%s %d %d" % (nm, e, f))
    for r in (4, 8):
        fn("toint_%d_%d_%d" % (e, f, r), one, r,
           "apfloat::to_int<u32:%d, u32:%d, u32:%d>(%s) as uN[%d]" % (e, f, r, a, r), "toint %d %d %d" % (e, f, r))
        fn("touint_%d_%d_%d" % (e, f, r), one, r,
           "apfloat::to_uint<u32:%d, u32:%d, u32:%d>(%s)" % (r, e, f, a), "touint %d %d %d" % (e, f, r))
        fn("tofixed_%d_%d_%d" % (e, f, r), one, r,
           "apfloat::cast_to_fixed<u32:%d, u32:%d, u32:%d>(%s) as uN[%d]" % (r, e, f, a, r), "tofixed %d %d %d" % (e, f, r))
    for n in (8, 12):
        for nm, call in (("fromfixed_rne", "cast_from_fixed_using_rne"), ("fromfixed_rz", "cast_from_fixed_using_rz")):
            fn("%s_%d_%d_%d" % (nm, e, f, n), [("x", "sN[%d]" % n, n)], W,
               fl("apfloat::%s<u32:%d, u32:%d, u32:%d>(x)" % (call, e, f, n)), "%s %d %d %d" % (nm, e, f, n))
    fn("ldexp_%d_%d" % (e, f), [("a", T, W), ("e", "sN[8]", 8)], W,
       fl("apfloat::ldexp%s(%s, e as s32)" % (P, a)), "ldexp %d %d" % (e, f))
    for we, wf in WIDE:
        if we >= e and wf >= f:
            WW = w(we, wf)
            src = un(we, wf, "a")
            arg = [("a", "uN[%d]" % WW, WW)]
            PP = "<u32:%d, u32:%d, u32:%d, u32:%d>" % (f, e, wf, we)
            fn("down_rne_%d_%d_to_%d_%d" % (we, wf, e, f), arg, W, fl("apfloat::downcast_rne%s(%s)" % (PP, src)),
               "down_rne %d %d %d %d" % (we, wf, e, f))
            fn("down_even_%d_%d_to_%d_%d" % (we, wf, e, f), arg, W,
               fl("apfloat::downcast%s(%s, apfloat::RoundStyle::TIES_TO_EVEN)" % (PP, src)),
               "down_even %d %d %d %d" % (we, wf, e, f))
            fn("down_away_%d_%d_to_%d_%d" % (we, wf, e, f), arg, W,
               fl("apfloat::downcast%s(%s, apfloat::RoundStyle::TIES_TO_AWAY)" % (PP, src)),
               "down_away %d %d %d %d" % (we, wf, e, f))
            UP = "<u32:%d, u32:%d, u32:%d, u32:%d>" % (we, wf, e, f)
            fn("up_%d_%d_to_%d_%d" % (e, f, we, wf), one, WW, fl("apfloat::upcast_with_denorms%s(%s)" % (UP, a)),
               "up %d %d %d %d" % (e, f, we, wf))
            fn("updaz_%d_%d_to_%d_%d" % (e, f, we, wf), one, WW, fl("apfloat::upcast_daz%s(%s)" % (UP, a)),
               "updaz %d %d %d %d" % (e, f, we, wf))

open(sys.argv[1], "w").write("\n".join(out))
open(sys.argv[2], "w").write("\n".join(tops) + "\n")
print("%d functions" % len(tops))
