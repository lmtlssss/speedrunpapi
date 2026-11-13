# 3.0 * 5.0, rounded up, as the first instruction at the target of a branch on NOEL-V.
# The branch is taken and the core predicts it not taken the first time. The instruction behind the branch is a
# double multiply; in a dual-issue configuration it is issued to the float unit with the branch and unissued
# when the branch resolves. The product at the target is exactly 15.0, 0x402e000000000000, with no flag.
# The program stores the product at s0, the float flags at s0 + 8, and a stop marker at s1.
# Defaults: FIRST is the wrong-path instruction, SECOND the one at the target, FCSR the rounding mode,
# PAD and TPAD shift the branch and the target by one instruction.
#ifndef FIRST
#define FIRST fmul.d f10, f3, f3
#endif
#ifndef SECOND
#define SECOND fmul.d f11, f1, f2
#endif
#ifndef FCSR
#define FCSR 0x60
#endif
#ifndef PAD
#define PAD 0
#endif
#ifndef TPAD
#define TPAD 0
#endif
        .option norelax
        .text
        .globl _start
_start:
        jal     t0, main                # t0 = address of trap
trap:   csrr    a2, mcause
        csrr    a3, mepc
        sd      a2, 16(s0)
        sd      a3, 24(s0)
        sd      x0, 0(s1)
1:      j       1b

main:   csrw    mtvec, t0
        lui     t0, 0x6
        csrs    mstatus, t0             # float unit on
        auipc   s0, 0x8                 # results go 0x8000 past here
        andi    s0, s0, -16
        auipc   s1, 0xf                 # a write 0xf000 past here stops the run
        andi    s1, s1, -16
        li      t1, -1
        srli    t1, t1, 2
        fmv.d.x f3, t1                  # 0x3fffffffffffffff
        li      t1, 0x4008
        slli    t1, t1, 48
        fmv.d.x f1, t1                  # 3.0
        li      t1, 0x4014
        slli    t1, t1, 48
        fmv.d.x f2, t1                  # 5.0
        li      t1, 0x401c
        slli    t1, t1, 48
        fmv.d.x f4, t1                  # 7.0
        li      t1, 0x402e
        slli    t1, t1, 48
        fmv.d.x f5, t1                  # 15.0
        li      t1, FCSR
        csrw    fcsr, t1                # rounding mode in bits 7..5, flags clear
        li      t2, 1
        nop
        nop
        nop
        nop
        .balign 8
        .rept   PAD
        nop
        .endr
        bnez    t2, target              # taken
        FIRST                           # wrong path
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        .balign 8
        .rept   TPAD
        nop
        .endr
target:
        SECOND
        fmv.x.d a0, f11
        csrr    a1, fflags
        sd      a0, 0(s0)
        sd      a1, 8(s0)
        sd      x0, 0(s1)
2:      j       2b
