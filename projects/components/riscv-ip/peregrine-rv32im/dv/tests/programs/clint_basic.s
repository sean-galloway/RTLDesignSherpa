# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# clint_basic.s -- peregrine CLINT and fence.i directed test (TASK-001
# stage 4), on the cached build (peregrine_top).  The interrupt pins are
# the CLINT's, so the program raises its own interrupts:
#
#   1. mtime runs: two reads, the second larger.
#   2. Timer: mtimecmp = mtime + 200, MTIE + MIE; the handler disarms
#      mtimecmp (high word all ones) and counts in s1.
#   3. Software: MSIE, msip = 1; the handler clears msip and counts in s2.
#   4. mip.MTIP with MIE = 0: arm mtimecmp in the past, see mip bit 7,
#      disarm, see it clear.  No trap is taken (s1 unchanged).
#   5. fence.i: overwrite an `addi a0, x0, 1` in .text with
#      `addi a0, x0, 2`, fence.i, run it: a0 must be 2.  Run once before
#      the store so the old word is in the I$.
#   6. fence.i patching the instruction right after it: that one was
#      already fetched, so fence.i must flush and refetch it.
#
# Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1, gp = the test number.

        .equ    CLINT_MSIP,   0x02000000
        .equ    CLINT_CMP_LO, 0x02004000
        .equ    CLINT_CMP_HI, 0x02004004
        .equ    CLINT_TIME_LO, 0x0200BFF8
        .equ    CLINT_TIME_HI, 0x0200BFFC
        .equ    SPIN,          4000

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        li      s1, 0
        li      s2, 0
        li      s3, 0                   # unexpected-trap count

# Test 1: mtime advances
        li      gp, 1
        li      t1, CLINT_TIME_LO
        lw      t2, 0(t1)
        nop
        nop
        nop
        lw      t3, 0(t1)
        bgeu    t2, t3, fail

# Test 2: a timer interrupt
        li      gp, 2
        li      t1, CLINT_CMP_HI
        li      t2, -1
        sw      t2, 0(t1)               # disarm while the low word moves
        li      t1, CLINT_TIME_LO
        lw      t2, 0(t1)
        addi    t2, t2, 200
        li      t1, CLINT_CMP_LO
        sw      t2, 0(t1)
        li      t1, CLINT_TIME_HI
        lw      t2, 0(t1)
        li      t1, CLINT_CMP_HI
        sw      t2, 0(t1)
        li      t0, 0x80                # MTIE
        csrw    mie, t0
        csrsi   mstatus, 8              # MIE
        li      t4, SPIN
1:      bnez    s1, 2f
        addi    t4, t4, -1
        bnez    t4, 1b
        j       fail
2:      li      t0, 1
        bne     s1, t0, fail

# Test 3: a software interrupt
        li      gp, 3
        li      t0, 0x8                 # MSIE
        csrw    mie, t0
        li      t1, CLINT_MSIP
        li      t2, 1
        sw      t2, 0(t1)
        li      t4, SPIN
1:      bnez    s2, 2f
        addi    t4, t4, -1
        bnez    t4, 1b
        j       fail
2:      li      t0, 1
        bne     s2, t0, fail
        lw      t2, 0(t1)               # the handler cleared msip
        bnez    t2, fail

# Test 4: MTIP pending with MIE = 0 is visible in mip, not taken
        li      gp, 4
        csrci   mstatus, 8
        li      t0, 0x80
        csrw    mie, t0
        li      t1, CLINT_CMP_LO
        sw      x0, 0(t1)
        li      t1, CLINT_CMP_HI
        sw      x0, 0(t1)               # mtimecmp = 0: pending now
        li      t4, SPIN
1:      csrr    t2, mip
        andi    t2, t2, 0x80
        bnez    t2, 2f
        addi    t4, t4, -1
        bnez    t4, 1b
        j       fail
2:      li      t2, -1
        sw      t2, 0(t1)               # disarm
        li      t4, SPIN
1:      csrr    t2, mip
        andi    t2, t2, 0x80
        beqz    t2, 2f
        addi    t4, t4, -1
        bnez    t4, 1b
        j       fail
2:      li      t0, 1
        bne     s1, t0, fail
        csrw    mie, x0

# Test 5: fence.i makes a store to .text visible to fetch
        li      gp, 5
        jal     ra, patched             # old word into the I$
        li      t0, 1
        bne     a0, t0, fail
        la      t1, patched
        la      t2, new_insn
        lw      t2, 0(t2)
        sw      t2, 0(t1)
        fence.i
        jal     ra, patched
        li      t0, 2
        bne     a0, t0, fail

# Test 6: fence.i makes a store visible to the very next instruction,
# which was already fetched (and is in the I$) when fence.i reached MEM.
        li      gp, 6
        la      t1, after_fi
        la      t2, new_insn2
        lw      t2, 0(t2)
        sw      t2, 0(t1)
        fence.i
after_fi:
        addi    a0, x0, 1
        li      t0, 3
        bne     a0, t0, fail

        bnez    s3, fail
        li      gp, 0
        j       pass

patched:
        addi    a0, x0, 1
        ret

fail:
        slli    t0, gp, 1
        ori     t0, t0, 1
        j       report
pass:
        li      t0, 1
report:
        la      t1, tohost
        sw      t0, 0(t1)
3:      j       3b

handler:
        csrr    t5, mcause
        li      t6, 0x80000007
        beq     t5, t6, h_timer
        li      t6, 0x80000003
        beq     t5, t6, h_soft
        addi    s3, s3, 1
        j       fail
h_timer:
        li      t5, CLINT_CMP_HI
        li      t6, -1
        sw      t6, 0(t5)
        addi    s1, s1, 1
        mret
h_soft:
        li      t5, CLINT_MSIP
        sw      x0, 0(t5)
        addi    s2, s2, 1
        mret

        .section .rodata
new_insn:
        addi    a0, x0, 2
new_insn2:
        addi    a0, x0, 3

        .section .data
        .align 3
        .globl tohost
tohost: .dword 0
        .globl fromhost
fromhost: .dword 0
