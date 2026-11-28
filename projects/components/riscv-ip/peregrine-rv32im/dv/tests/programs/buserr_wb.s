# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# buserr_wb.s -- the imprecise bus-error report (riscv-ip/peregrine-rv32im
# TASK-005, amber TASK-008): a dirty line whose write-back is answered
# SLVERR is dropped by amber, its address is latched in amber's sticky
# status, and peregrine takes platform interrupt 16 (mcause 0x8000_0010)
# and reads / clears the status through the custom CSR mbuserr (0x7C0):
# [31:2] the line address, bit 1 overflow, bit 0 valid.
#
# The TB memory (peregrine_sys_tb_top) answers WRITES to addresses with bits
# 27:24 = 0xC with SLVERR and reads them OKAY; it aliases 0x8C00_xxxx onto
# 0x8000_xxxx, so a dropped line reads back as the memory word behind it.
# spike has no mbuserr, so this program runs without lockstep: it checks
# itself, and the TB holds its CSR reads to the shadow model.
#
# The handler takes only interrupt 16: it reads and clears mbuserr in one
# csrrw, logs {mcause, mepc, mbuserr} (s3 counts), and returns.  Anything
# else fails.  Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1.
#
#   1  an eviction's write-back fails: interrupt, address, line dropped
#   2  two clean-all write-backs fail with interrupts off: the first
#      address and the overflow bit, mip.16 pending, a write clears both
#   3  a clean-all write-back fails with interrupts on: the interrupt
#      follows the fence.i
#   4  mie.16 masks it; enabling mie.16 takes it

        .equ    WB_ERR,  0x8C000000     # write-back error window (reads OK)
        .equ    RAM,     0x80000000     # the same memory words
        .equ    WAY,     0x2000         # amber: 128 sets x 64 B per way
        .equ    MIE_BE,  0x10000        # mie / mip bit 16
        .equ    CAUSE,   0x80000010
        .equ    WAIT,    4000

        .macro  WAIT_IRQ n
        li      t1, WAIT
1:      li      t5, \n
        beq     s3, t5, 2f
        addi    t1, t1, -1
        bnez    t1, 1b
        j       fail
2:
        .endm

# LOG_IS n, info: entry n (0-based) is {CAUSE, -, info}
        .macro  LOG_IS n, info
        la      t0, log
        lw      t6, (12 * \n)(t0)
        li      t5, CAUSE
        bne     t6, t5, fail
        lw      t6, (12 * \n + 8)(t0)
        li      t5, \info
        bne     t6, t5, fail
        .endm

# DROPPED off: the WB_ERR line reads as memory, not as what was stored
        .macro  DROPPED off, stored
        li      t1, WB_ERR + \off
        lw      t3, 0(t1)
        li      t1, RAM + \off
        lw      t4, 0(t1)
        bne     t3, t4, fail
        li      t5, \stored
        beq     t3, t5, fail
        .endm

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        la      s2, log
        li      s3, 0
        li      t0, MIE_BE
        csrw    mie, t0

# Test 1: a dirty line evicted; its write-back fails
        li      gp, 1
        csrsi   mstatus, 8
        li      t1, WB_ERR + 0x40       # set 1
        li      t2, 0xDEAD0001
        sw      t2, 0(t1)               # write-allocate fill (reads OK): M
        li      t1, RAM + 0x40 + WAY    # eight more lines in set 1
        li      t2, 8
3:      lw      t3, 0(t1)
        li      t4, WAY
        add     t1, t1, t4
        addi    t2, t2, -1
        bnez    t2, 3b
        WAIT_IRQ 1
        LOG_IS  0, (WB_ERR + 0x40) | 1
        csrr    t0, mip
        li      t5, MIE_BE
        and     t0, t0, t5
        bnez    t0, fail                # cleared by the handler's write
        DROPPED 0x40, 0xDEAD0001

# Test 2: two clean-all write-backs fail, interrupts off
        li      gp, 2
        csrci   mstatus, 8
        li      t1, WB_ERR + 0x80       # set 2
        li      t2, 0xDEAD0002
        sw      t2, 0(t1)
        li      t1, WB_ERR + 0xC0       # set 3
        li      t2, 0xDEAD0003
        sw      t2, 0(t1)
        fence.i                         # amber clean-all: both WriteCleans fail
        li      t1, 200
4:      addi    t1, t1, -1
        bnez    t1, 4b
        bnez    s3, 5f                  # still masked: the count stays 1
        j       fail
5:      li      t5, 1
        bne     s3, t5, fail
        csrr    t0, mip
        li      t5, MIE_BE
        and     t0, t0, t5
        beqz    t0, fail                # pending
        csrr    t0, 0x7c0               # read without clearing
        li      t5, (WB_ERR + 0x80) | 3 # the first (set 2), overflow, valid
        bne     t0, t5, fail
        csrr    t0, 0x7c0               # a read does not clear
        bne     t0, t5, fail
        csrw    0x7c0, x0               # clear
        csrr    t0, 0x7c0
        andi    t0, t0, 3
        bnez    t0, fail
        csrr    t0, mip
        li      t5, MIE_BE
        and     t0, t0, t5
        bnez    t0, fail
        DROPPED 0x80, 0xDEAD0002
        DROPPED 0xC0, 0xDEAD0003
        csrsi   mstatus, 8              # nothing pending: no interrupt
        li      t1, 100
6:      addi    t1, t1, -1
        bnez    t1, 6b
        li      t5, 1
        bne     s3, t5, fail

# Test 3: a clean-all write-back fails, interrupts on
        li      gp, 3
        li      t1, WB_ERR + 0x100      # set 4
        li      t2, 0xDEAD0004
        sw      t2, 0(t1)
        fence.i
        WAIT_IRQ 2
        LOG_IS  1, (WB_ERR + 0x100) | 1
        DROPPED 0x100, 0xDEAD0004

# Test 4: mie.16 masks the interrupt; enabling it takes it
        li      gp, 4
        csrw    mie, x0
        li      t1, WB_ERR + 0x140      # set 5
        li      t2, 0xDEAD0005
        sw      t2, 0(t1)
        fence.i
        li      t1, 200
7:      addi    t1, t1, -1
        bnez    t1, 7b
        li      t5, 2
        bne     s3, t5, fail            # masked
        li      t0, MIE_BE
        csrw    mie, t0
        WAIT_IRQ 3
        LOG_IS  2, (WB_ERR + 0x140) | 1
        DROPPED 0x140, 0xDEAD0005

        j       pass

fail:
        csrci   mstatus, 8
        slli    t1, gp, 1
        ori     t1, t1, 1
        j       report
pass:
        csrci   mstatus, 8
        li      t1, 1
report:
        la      t0, tohost
1:      sw      t1, 0(t0)
        j       1b

# The handler owns a0 and a1, and t0 through mscratch.
        .align 2
handler:
        csrrw   t0, mscratch, t0
        csrr    a0, mcause
        li      a1, CAUSE
        bne     a0, a1, fail
        sw      a0, 0(s2)
        csrr    a1, mepc
        sw      a1, 4(s2)
        csrrw   a1, 0x7c0, x0           # read and clear the status
        sw      a1, 8(s2)
        addi    s2, s2, 12
        addi    s3, s3, 1
        csrrw   t0, mscratch, t0
        mret

        .section .data
        .align 3
        .globl tohost
tohost: .dword 0
        .globl fromhost
fromhost: .dword 0
        .align 4
log:    .space  12 * 16
