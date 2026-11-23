# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# irq_basic.s -- peregrine machine-interrupt directed test (TASK-001 stage 1).
#
# The TB drives the three interrupt pins from the last value stored to
# `irq_ctrl`: bit 0 MSIP, bit 1 MTIP, bit 2 MEIP.  Bit 3 is "auto timer":
# while it is set the TB re-raises MTIP a fixed number of cycles after
# each store that clears bit 1.  irq_ctrl is ordinary RAM, so the handler
# reads it back, clears the bit it serviced, and stores it again.
#
# The handler logs every mcause into `irq_log` (s3 counts entries) and owns
# s4-s6; the main program never uses them.  Any synchronous exception in
# the handler path is a failure.  Pass: tohost = 1.  Fail: tohost =
# (gp << 1) | 1, gp = the test number.

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        la      s0, irq_ctrl
        la      s2, irq_log
        li      s3, 0
        li      t0, 0x888               # MSIE | MTIE | MEIE
        csrw    mie, t0

# Test 1: a pending MTI is not taken while mstatus.MIE = 0.
        li      gp, 1
        li      t0, 2
        sw      t0, 0(s0)
        li      t1, 20
1:      addi    t1, t1, -1
        bnez    t1, 1b
        bnez    s3, fail

# Test 2: setting mstatus.MIE takes it, once, with mcause = 0x80000007.
        li      gp, 2
        csrsi   mstatus, 8
        li      t1, 20
1:      addi    t1, t1, -1
        bnez    t1, 1b
        li      t0, 1
        bne     s3, t0, fail
        lw      t0, 0(s2)
        li      t1, 0x80000007
        bne     t0, t1, fail
        csrr    t0, mip
        andi    t0, t0, 0x80            # MTIP must be clear now
        bnez    t0, fail

# Test 3: all three pending at once are taken MEI, MSI, MTI.
        li      gp, 3
        csrci   mstatus, 8
        li      s3, 0
        li      t0, 7
        sw      t0, 0(s0)
        csrsi   mstatus, 8
        li      t1, 30
1:      addi    t1, t1, -1
        bnez    t1, 1b
        li      t0, 3
        bne     s3, t0, fail
        lw      t0, 0(s2)
        li      t1, 0x8000000b
        bne     t0, t1, fail
        lw      t0, 4(s2)
        li      t1, 0x80000003
        bne     t0, t1, fail
        lw      t0, 8(s2)
        li      t1, 0x80000007
        bne     t0, t1, fail

# Test 4: precision under fire.  The auto timer interrupts a loop of
# loads, stores, load-use pairs and taken branches; every result must be
# exact and the interrupts must actually have landed.
        li      gp, 4
        li      s3, 0
        li      t0, 0xA                 # auto timer + MTIP
        sw      t0, 0(s0)
        la      a0, scratch
        li      a1, 0                   # running sum
        li      a2, 1                   # i
        li      a3, 201
2:      andi    t0, a2, 15
        slli    t0, t0, 2
        add     t0, t0, a0
        lw      t1, 0(t0)               # old slot value
        add     t1, t1, a2              # slot += i (load-use)
        sw      t1, 0(t0)
        add     a1, a1, a2
        addi    a2, a2, 1
        bne     a2, a3, 2b
        sw      zero, 0(s0)             # stop the timer
        li      t1, 20100               # sum 1..200
        bne     a1, t1, fail
        li      t2, 0                   # the 16 slots must also sum to 20100
        li      t3, 16
        mv      t0, a0
3:      lw      t4, 0(t0)
        add     t2, t2, t4
        addi    t0, t0, 4
        addi    t3, t3, -1
        bnez    t3, 3b
        bne     t2, t1, fail
        li      t0, 4
        blt     s3, t0, fail            # at least four interrupts landed

pass:
        li      t0, 1
        la      t1, tohost
        sw      t0, 0(t1)
1:      j       1b

fail:
        slli    t0, gp, 1
        ori     t0, t0, 1
        la      t1, tohost
        sw      t0, 0(t1)
1:      j       1b

# --- handler -------------------------------------------------------------
        .balign 4
handler:
        csrr    s4, mcause
        bgez    s4, fail                # a synchronous exception: fail
        slli    s5, s3, 2
        add     s5, s5, s2
        sw      s4, 0(s5)
        addi    s3, s3, 1
        andi    s4, s4, 0x1f
        li      s5, 1                   # code 3 (MSI) -> bit 0
        li      s6, 3
        beq     s4, s6, 4f
        li      s5, 2                   # code 7 (MTI) -> bit 1
        li      s6, 7
        beq     s4, s6, 4f
        li      s5, 4                   # code 11 (MEI) -> bit 2
4:      lw      s6, 0(s0)
        not     s5, s5
        and     s6, s6, s5
        sw      s6, 0(s0)
        mret

        .section .data
        .balign 64
tohost: .word 0
        .balign 64
irq_ctrl:
        .word 0
        .balign 64
scratch:
        .space 64
irq_log:
        .space 1024
