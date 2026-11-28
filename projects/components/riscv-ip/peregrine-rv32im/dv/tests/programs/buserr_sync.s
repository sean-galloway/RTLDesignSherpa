# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# buserr_sync.s -- peregrine's synchronous bus-error traps (riscv-ip/
# peregrine-rv32im TASK-005) on the cached build: load and store access
# faults from the uncached port and from amber's fills, and instruction
# access faults from the I$, each taken precisely with mepc / mcause /
# mtval checked.
#
# The TB memory (peregrine_sys_tb_top) answers by address bits 27:24:
# 0xE DECERR, 0xD SLVERR (reads and writes).  The addresses below are in
# the uncached window (0x1D.. / 0x1E..), the cacheable space (0x4D.. /
# 0x4E.., amber) and, for fetches, the I$.  spike maps none of them, so
# it takes the same faults: the program runs in spike lockstep.
#
# The handler logs {mcause, mepc, mtval} per trap at `log` (s3 counts
# entries), returns past the faulting instruction (mepc + 4), or for an
# instruction access fault to ra (the jalr that went there).  Any other
# trap cause fails.  Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1.
#
#   1-3  uncached: lw DECERR, sw SLVERR, lh SLVERR at a halfword offset
#        (mtval is the byte address); rd keeps its old value.
#   4-6  amber: a load whose fill fails, again (the line was not
#        installed, so it misses and fails again), a store miss whose
#        write-allocate fill fails (sb, byte offset), lbu SLVERR.
#   7    precision: the instruction after a faulting load (an addi) and
#        a store after it run exactly once, after the handler; a store and
#        a load directly behind a faulting access are not accepted while
#        its error response arrives.
#   8    a faulting access accepted while an I$ refill holds the core
#        (uncached and amber), at three offsets so one lines up.
#   9-11 instruction access faults: jalr into a DECERR line, a SLVERR
#        line, and a target in the middle of a line.

        .equ    UC_DEC,  0x1E000010
        .equ    UC_SLV,  0x1D000020
        .equ    DC_DEC,  0x4E000040
        .equ    DC_SLV,  0x4D000100
        .equ    IF_DEC,  0x4E000200
        .equ    IF_SLV,  0x4D000300
        .equ    IF_MID,  0x4E000444

        .equ    C_IFAULT, 1
        .equ    C_LFAULT, 5
        .equ    C_SFAULT, 7

# CHECK cause, label, tval-register: the last log entry is
# {cause, address of label, tval}, and it is entry number s4.
        .macro  CHECK cause, epc, tval
        addi    s4, s4, 1
        bne     s3, s4, fail
        addi    t0, s2, -12
        lw      t6, 0(t0)
        li      t5, \cause
        bne     t6, t5, fail
        lw      t6, 4(t0)
        la      t5, \epc
        bne     t6, t5, fail
        lw      t6, 8(t0)
        bne     t6, \tval, fail
        .endm

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        la      s2, log
        li      s3, 0                   # trap count (the handler's)
        li      s4, 0                   # trap count expected so far
        la      s0, data

# Test 1: uncached load, DECERR: load access fault, rd not written
        li      gp, 1
        li      t1, UC_DEC
        li      s1, 0x5A5A5A5A
t1_ld:  lw      s1, 0(t1)
        CHECK   C_LFAULT, t1_ld, t1
        li      t5, 0x5A5A5A5A
        bne     s1, t5, fail

# Test 2: uncached store, SLVERR: store access fault
        li      gp, 2
        li      t1, UC_SLV
        li      t2, 0x12345678
t2_st:  sw      t2, 0(t1)
        CHECK   C_SFAULT, t2_st, t1

# Test 3: uncached lh at a halfword offset, SLVERR: mtval is the byte address
        li      gp, 3
        li      t1, UC_SLV + 6
        li      s1, 0x0000ABCD
t3_ld:  lh      s1, 0(t1)
        CHECK   C_LFAULT, t3_ld, t1
        li      t5, 0x0000ABCD
        bne     s1, t5, fail

# Test 4: amber load miss, the fill DECERR; again: still not installed
        li      gp, 4
        li      t1, DC_DEC
        li      s1, 0x77777777
t4_ld:  lw      s1, 0(t1)
        CHECK   C_LFAULT, t4_ld, t1
t4_ld2: lw      s1, 4(t1)
        addi    t1, t1, 4
        CHECK   C_LFAULT, t4_ld2, t1
        li      t5, 0x77777777
        bne     s1, t5, fail
        lw      t2, 0(s0)               # an ordinary load still works
        li      t5, 0xC0FFEE00
        bne     t2, t5, fail

# Test 5: amber store miss (write-allocate fill) DECERR, a byte store
        li      gp, 5
        li      t1, DC_DEC + 0x43       # another line, byte 3 of a word
        li      t2, 0xA5
t5_st:  sb      t2, 0(t1)
        CHECK   C_SFAULT, t5_st, t1

# Test 6: amber lbu, SLVERR
        li      gp, 6
        li      t1, DC_SLV + 3
t6_ld:  lbu     s1, 0(t1)
        CHECK   C_LFAULT, t6_ld, t1

# Test 7: precision. The addi and the sw behind the faulting load run once.
        li      gp, 7
        li      s5, 0
        sw      x0, 4(s0)
        li      t1, DC_DEC + 0x80
        li      t2, 0x3C3C
t7_ld:  lw      s1, 0(t1)
        addi    s5, s5, 1
        sw      t2, 4(s0)
        lw      t3, 4(s0)
        add     s5, s5, t3              # 1 + 0x3C3C, or more if run twice
        CHECK   C_LFAULT, t7_ld, t1
        li      t5, 0x3C3D
        bne     s5, t5, fail
        li      t1, UC_DEC + 0x40
t7_ld2: lw      s1, 0(t1)
        addi    s5, s5, 1
        CHECK   C_LFAULT, t7_ld2, t1
        li      t5, 0x3C3E
        bne     s5, t5, fail
        # A store and a load right behind a faulting access: in MEM while the
        # error response arrives, they must not be accepted then (the TB's
        # request count sees an extra access; the store would also land
        # before its trap-free re-execution).
        li      t1, UC_DEC + 0x80
        li      t2, 0x7E7E
t7_ld3: lw      s1, 0(t1)
        sw      t2, 8(s0)
        CHECK   C_LFAULT, t7_ld3, t1
        li      t1, DC_DEC + 0xC0
t7_ld4: lw      s1, 0(t1)
        lw      t3, 8(s0)
        CHECK   C_LFAULT, t7_ld4, t1
        li      t5, 0x7E7E
        bne     t3, t5, fail

# Test 8: a faulting access in MEM while fetch crosses into a line the I$
# has never held (offsets 48, 52, 56 in a fresh line); the refill holds
# the core, the access is accepted under the hold and its error response
# may arrive during the refill.
        li      gp, 8
        li      s6, UC_DEC + 0x100
        li      s7, DC_DEC + 0x200
        j       blk0
        .align 6
blk0:   .rept   12
        nop
        .endr
t8_a:   lw      s1, 0(s6)               # offset 48
        .align 6
        CHECK   C_LFAULT, t8_a, s6
        j       blk1
        .align 6
blk1:   .rept   13
        nop
        .endr
t8_b:   lw      s1, 0(s6)               # offset 52
        .align 6
        CHECK   C_LFAULT, t8_b, s6
        j       blk2
        .align 6
blk2:   .rept   14
        nop
        .endr
t8_c:   lw      s1, 0(s6)               # offset 56
        .align 6
        CHECK   C_LFAULT, t8_c, s6
        j       blk3
        .align 6
blk3:   .rept   13
        nop
        .endr
t8_d:   lw      s1, 0(s7)               # amber, offset 52
        .align 6
        CHECK   C_LFAULT, t8_d, s7
        j       blk4
        .align 6
blk4:   .rept   14
        nop
        .endr
t8_e:   sw      s1, 0(s7)               # amber store, offset 56
        .align 6
        CHECK   C_SFAULT, t8_e, s7

# Test 9: instruction access fault, DECERR line
        li      gp, 9
        li      t1, IF_DEC
        jalr    ra, 0(t1)
        CHECK   C_IFAULT, IF_DEC, t1

# Test 10: instruction access fault, SLVERR line
        li      gp, 10
        li      t1, IF_SLV
        jalr    ra, 0(t1)
        CHECK   C_IFAULT, IF_SLV, t1

# Test 11: instruction access fault, a target in the middle of a line;
# then the same target again (the line was not installed)
        li      gp, 11
        li      t1, IF_MID
        jalr    ra, 0(t1)
        CHECK   C_IFAULT, IF_MID, t1
        jalr    ra, 0(t1)
        CHECK   C_IFAULT, IF_MID, t1

        j       pass

fail:
        slli    t1, gp, 1
        ori     t1, t1, 1
        j       report
pass:
        li      t1, 1
report:
        la      t0, tohost
1:      sw      t1, 0(t0)
        j       1b

# The handler owns t0 (saved in mscratch), a0 and a1.
        .align 2
handler:
        csrrw   t0, mscratch, t0
        csrr    a0, mcause
        sw      a0, 0(s2)
        csrr    a1, mepc
        sw      a1, 4(s2)
        csrr    a1, mtval
        sw      a1, 8(s2)
        addi    s2, s2, 12
        addi    s3, s3, 1
        li      a1, C_IFAULT
        beq     a0, a1, 2f
        li      a1, C_LFAULT
        beq     a0, a1, 1f
        li      a1, C_SFAULT
        beq     a0, a1, 1f
        j       fail
1:      csrr    a1, mepc                # load / store: skip it
        addi    a1, a1, 4
        csrw    mepc, a1
        j       3f
2:      csrw    mepc, ra                # fetch: back to the jalr's link
3:      csrrw   t0, mscratch, t0
        mret

        .section .data
        .align 3
        .globl tohost
tohost: .dword 0
        .globl fromhost
fromhost: .dword 0
data:   .word   0xC0FFEE00
        .word   0
        .align 4
log:    .space  12 * 32
