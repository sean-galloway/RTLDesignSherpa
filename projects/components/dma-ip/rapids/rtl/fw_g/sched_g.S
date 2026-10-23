# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# sched_g.S -- rapids-g scheduler firmware (rapids TASK-034, TASK-037), RV32I.
#
# Every gatling hart runs this same image (contexts are implicit): it serves
# the one or two scheduler_g slots rapids_seq_g aliases to it. It is an
# executive (the poll and `step`) over a policy table (`ptab` and its rows):
# each pass of the poll gives a slot one handler, which does one step of the
# FSM scheduler's next-state logic -- or the EXT run-base arithmetic the FSM
# scheduler does in hardware -- and returns. The beat totals are hardware in
# scheduler_g. Faults and channel resets are hardware interlocks; nothing
# here handles them, and CH_ERROR raises no attn.
#
# The run bases mirror stream_run_addr_gen + dma_address_gen exactly:
# base + ((i0*s0) & m0) + ((i1*s1) & m1), 64-bit, with the products kept as
# running sums (no multiplier), the 16-bit index wrap of i1 included.
#
# Built by bin/gen_rapids_g_fw.py into rtl/macro_g/generated/fw/sched_g_fw.svh.
# No stack, no .data: state that outlives one step lives in the per-hart
# scratch.

        .equ MMIO,          0x10000000
        .equ GLOBAL,        0x10001000
        .equ SCRATCH,       0x20000000
        .equ SLOT_STRIDE,   0x100       # window and scratch, per slot
        .equ WR_BLOCK,      0x80        # scratch: read block, then write block

        # scheduler_g window, byte offsets (reads)
        .equ R_STATUS,      0
        .equ R_SRC_LO,      4
        .equ R_DST_LO,      12
        .equ R_LEN,         20
        .equ R_EXT0,        28          # rd_stride_0; the write side is +12
        .equ R_FIFO,        52
        .equ R_CFG,         56
        .equ R_HEAD_FLAGS,  72          # descriptor [223:192]: valid [0], opcode [17:16], type [20:18], op [24]
        .equ R_RD_TOTAL,    76          # the beat totals (hardware, loaded on the take)
        .equ R_WR_TOTAL,    80
        .equ R_HEAD_SUM,    84          # the head: valid [0], last [1], next_ptr != 0 [2], open [3]
        .equ R_ALG,         88          # the latched descriptor's next-address selector [7:0]
        # (writes)
        .equ W_CMD,         0
        .equ W_FW_ERROR,    4           # a firmware error packet, data {word, PKT_LO}
        .equ W_RD_BASE_LO,  12
        .equ W_WR_BASE_LO,  20
        # The highest next-address selector this image implements (rapids
        # TASK-035): 0 stream_run_addr_gen bases, 1 Z-order. gen_rapids_g_fw.py
        # copies it into the image's svh (FW_ALG_MAX), and scheduler_g refuses
        # a descriptor above it -- in hardware, from reset.
        .equ ALG_MAX,       1

        # STATUS bits
        .equ B_HEAD,        8
        .equ B_ENABLE,      9
        .equ B_VALID,       11
        .equ B_LAST,        14
        .equ B_CHAIN,       16
        .equ B_TILE_BAD,    17
        .equ B_EXEC_DONE,   19
        .equ B_PENDING,     20
        .equ B_EXT,         22
        .equ B_HDR_ONLY,    23
        .equ B_RD_PER_BEAT, 24
        .equ B_WR_PER_BEAT, 25
        .equ B_RD_DONE,     26
        .equ B_WR_DONE,     27
        .equ B_ARMED,       28
        .equ B_STAGED,      29
        .equ B_GEN_NEED,    30          # an EXT descriptor taken by the hardware: set its bases up
        .equ B_DECLINED,    31
        # CFG bits
        .equ C_EN_READ,     20
        .equ C_EN_WRITE,    21
        # CMD bits beside the state
        .equ CMD_RD_DONE,   0x100
        .equ CMD_WR_DONE,   0x200
        .equ CMD_STAGE,     0x400       # the head is validated: the hardware takes it
        .equ CMD_ARM,       0x800       # complete this descriptor on exec_complete ...
        .equ CMD_ARM_NEXT,  0x1000      # ... then NEXT_DESC (else IDLE)
        .equ CMD_GEN_OK,    0x2000      # run bases set up
        .equ CMD_DECLINE,   0x4000      # the head fails: the normal path takes it to CH_ERROR
        .equ CMD_STAGE_ARM, 0x8000      # with STAGE: the head is taken already armed ...
        .equ CMD_STAGE_ARM_NEXT, 0x10000  # ... for NEXT_DESC (else IDLE)
        .equ SCR_LINK,      0xF8        # slot scratch: ext_init's return address
        .equ SCR_STATUS,    0xF4        # slot scratch: refill_both's STATUS snapshot

        # channel states (rapids_pkg::channel_state_t, one-hot)
        .equ ST_IDLE,       0x01
        .equ ST_FETCH,      0x02
        .equ ST_XFER,       0x04
        .equ ST_COMPLETE,   0x08
        .equ ST_NEXT,       0x10
        .equ ST_ERROR,      0x20

        # run-base generator block in scratch, byte offsets
        .equ G_BASE_LO,     0
        .equ G_BASE_HI,     4
        .equ G_ACC0_LO,     8           # i0 * s0, running
        .equ G_ACC0_HI,     12
        .equ G_ACC1_LO,     16          # i1 * s1, running
        .equ G_ACC1_HI,     20
        .equ G_S0_LO,       24          # strides, sign-extended to 64 bits
        .equ G_S0_HI,       28
        .equ G_S1_LO,       32
        .equ G_S1_HI,       36
        .equ G_M0_LO,       40          # wrap masks (all ones = no wrap)
        .equ G_M0_HI,       44
        .equ G_M1_LO,       48
        .equ G_M1_HI,       52
        .equ G_I0,          56
        .equ G_I1,          60
        .equ G_INNER,       64
        .equ G_GEN,         68          # beats covered by the bases so far
        .equ G_TOTAL,       72
        .equ G_STEP,        76
        .equ G_PER_BEAT,    80
        .equ G_NOWRAP,      84          # 1: ACC0/ACC1 hold cur/row addresses (fast path);
                                        # -1: selector 1, Z-order (I0 is the position k)

# bit test: \rd = (\rs >> \bit) & 1
        .macro BIT rd, rs, bit
        srli    \rd, \rs, \bit
        andi    \rd, \rd, 1
        .endm

# store the 64-bit wrap mask for log2 size \w at \off(a2); clobbers t5, gp
        .macro MASK w, off
        beqz    \w, 93f
        li      t5, 32
        bgeu    \w, t5, 92f
        li      t5, 1                   # 1..31: lo = (1 << w) - 1, hi = 0
        sll     t5, t5, \w
        addi    t5, t5, -1
        sw      t5, \off(a2)
        sw      zero, \off+4(a2)
        j       94f
92:     addi    t5, \w, -32             # 32..63: lo = all ones
        li      gp, 1
        sll     gp, gp, t5
        addi    gp, gp, -1
        sw      gp, \off+4(a2)
        li      t5, -1
        sw      t5, \off(a2)
        j       94f
93:     li      t5, -1                  # 0: no wrap
        sw      t5, \off(a2)
        sw      t5, \off+4(a2)
94:
        .endm

        .option norelax                 # step's jalr off x0 + %lo(ptab): linker
                                        # relaxation would rewrite its base to x0
        .text
        .globl  _start
_start:
        li      s0, MMIO
        li      s1, GLOBAL
        li      s2, SCRATCH

# The firmware is an executive and a policy table (rapids TASK-037).
#
# Executive: run to completion, no preemption -- the barrel's harts are the
# threads. Each pass polls one slot's events in fixed priority: an open head
# first (judged inline, JUDGE), then SUMMARY attn, which calls `step` once.
# `step` reads STATUS and jumps through `ptab`, indexed by the one-hot state,
# to that state's row of the policy table; the row picks ONE handler by its
# event and the handler returns straight to the poll. No handler loops or
# re-dispatches, so none can hold a hart: the next step of a slot is always
# the next pass of the poll.
#
# Policy table (state, event -> handler):
#   any         open head                 judge_head   (inline in the poll)
#   IDLE, NEXT  declined head             fetch_start  (-> FETCH_DESC)
#   IDLE, NEXT  open head                 judge_head
#   FETCH_DESC  tile_bad or invalid       fetch_error  (-> ERROR)
#   XFER_DATA   GEN_NEED                  ext_start    (GEN_OK, then set the bases up)
#   XFER_DATA   EXT, bases not done       ext_refill
#   FETCH_DESC valid, XFER_DATA or COMPLETE unarmed: never (every valid head
#               is staged armed)          fw_fault     (FW_ERROR packet, -> ERROR)
#   other                                 nothing (the hardware is moving)
# The next-address algorithm (rapids TASK-035) is a row below this one: the
# generator routines ext_init / refill are what ext_start and ext_refill
# call.

# JUDGE (judge_head): t3 = HEAD_SUM (open), a0 = the window. A valid head is
# staged armed with its own chain outcome (next_ptr != 0 && !last ->
# NEXT_DESC, else IDLE), so the hardware takes it at IDLE / NEXT_DESC and
# completes it without the firmware; an invalid one is declined (the normal
# path takes it to CH_ERROR, as the FSM would). Clobbers t4, t5.
        .macro JUDGE
        andi    t4, t3, 1
        li      t5, CMD_DECLINE
        beqz    t4, 95f
        andi    t4, t3, 6               # {chain, last} == {1, 0}?
        xori    t4, t4, 4
        seqz    t4, t4
        slli    t4, t4, 16              # CMD_STAGE_ARM_NEXT
        li      t5, CMD_STAGE | CMD_STAGE_ARM
        or      t5, t5, t4
95:     sw      t5, W_CMD(a0)
        .endm

        lw      t0, 4(s1)               # SLOTS: one slot per hart takes the
        addi    t0, t0, -1              # tight poll below, two the unrolled
        bnez    t0, multi               # poll, more the slot loop

# One slot per hart (NUM_HARTS == NUM_CHANNELS): every instruction costs
# NUM_HARTS clocks, so the chain hook is four instructions from the HEAD_SUM
# read to the CMD write. HEAD_SUM == 13 is an open, valid head with
# next_ptr != 0 and !last: stage it armed for NEXT_DESC with the word held
# in tp (a handler may clobber tp, so it is reloaded after every step). Any
# other open head takes JUDGE; no open head and no attn loops.
        li      tp, CMD_STAGE | CMD_STAGE_ARM | CMD_STAGE_ARM_NEXT
        j       one_loop
one_chain:
        sw      tp, W_CMD(s0)
one_loop:
        lw      t3, R_HEAD_SUM(s0)
        addi    t4, t3, -13
        beqz    t4, one_chain
        andi    t4, t3, 8
        bnez    t4, one_judge
        lw      t0, 0(s1)               # SUMMARY
        beqz    t0, one_loop            # the idle pass: 7 instructions
        lw      t3, R_HEAD_SUM(s0)      # a head that came after the first read
        andi    t4, t3, 8               # is judged here, not by the longer
        bnez    t4, one_judge           # IDLE / NEXT_DESC row
        mv      a0, s0
        mv      a1, s2
        jal     ra, step
        li      tp, CMD_STAGE | CMD_STAGE_ARM | CMD_STAGE_ARM_NEXT
        j       one_loop
one_judge:
        mv      a0, s0
        JUDGE
        j       one_loop

multi:
        addi    t0, t0, -1
        bnez    t0, slot_loop

# Two slots per hart: the same poll, slot 0 then slot 1, one step each.
main_loop:
        lw      t0, 0(s1)               # SUMMARY: attn of this hart's slots
        beqz    t0, main_loop
        andi    t1, t0, 1
        beqz    t1, 1f
        mv      a0, s0
        lw      t3, R_HEAD_SUM(a0)
        andi    t4, t3, 8
        beqz    t4, 2f
        JUDGE
        j       1f
2:      mv      a1, s2
        jal     ra, step
1:      andi    t1, t0, 2
        beqz    t1, main_loop
        addi    a0, s0, SLOT_STRIDE
        lw      t3, R_HEAD_SUM(a0)
        andi    t4, t3, 8
        beqz    t4, 3f
        JUDGE
        j       main_loop
3:      addi    a1, s2, SLOT_STRIDE
        jal     ra, step
        j       main_loop

# Three or more slots per hart (16 channels on 4 harts): the same poll as a
# loop over SUMMARY's bits, one step per slot with attention. sp holds the
# slot's offset (window and scratch share SLOT_STRIDE); step preserves t0,
# sp, s0-s2.
slot_loop:
        lw      t0, 0(s1)               # SUMMARY
        beqz    t0, slot_loop
        li      sp, 0
1:      andi    t1, t0, 1
        beqz    t1, 3f
        add     a0, s0, sp
        lw      t3, R_HEAD_SUM(a0)
        andi    t4, t3, 8
        beqz    t4, 2f
        JUDGE
        j       3f
2:      add     a1, s2, sp
        jal     ra, step
3:      srli    t0, t0, 1
        addi    sp, sp, SLOT_STRIDE
        bnez    t0, 1b
        j       slot_loop

# step: a0 = slot window, a1 = slot scratch, ra = the poll. Preserves t0,
# s0-s2, sp, ra. One handler, chosen by the state's row of ptab, then back.
# A CMD write lands before this hart's next instruction (NUM_HARTS >= 4
# cycles), so a handler that writes CMD and returns leaves the next pass a
# STATUS that already shows it.
step:
        lw      t2, R_STATUS(a0)
        andi    t3, t2, 0x3f            # the one-hot state
        slli    t3, t3, 2
        jalr    zero, t3, %lo(ptab)     # ptab is below 2 KB (checked below)

# ptab: one jump per value of the one-hot state field (64 entries, so no
# value can index past it); a value that is not a state does nothing. The
# image is linked at 0, so ptab's address fits jalr's 12-bit offset from
# the index alone and step needs no base register (bin/gen_rapids_g_fw.py
# refuses an image whose ptab_end is above 2 KB).
ptab:
        ret                             # 0x00 (no state)
        j       row_idle                # 0x01 IDLE
        j       row_fetch               # 0x02 FETCH_DESC
        ret
        j       row_xfer                # 0x04 XFER_DATA
        .rept 3
        ret
        .endr
        j       row_complete            # 0x08 COMPLETE
        .rept 7
        ret
        .endr
        j       row_next                # 0x10 NEXT_DESC
        .rept 15
        ret
        .endr
        .rept 32                        # 0x20 ERROR (left only by a channel
        ret                             # reset) and the non-states above it
        .endr
ptab_end:

# --- the rows: each picks one handler by event, highest priority first ---

row_xfer:
        BIT     t3, t2, B_ARMED         # never unarmed: every head is staged
        beqz    t3, fw_fault            # armed (see fw_fault)
        BIT     t3, t2, B_GEN_NEED
        bnez    t3, ext_start
        BIT     t3, t2, B_EXT
        beqz    t3, h_ret
ext_refill:                             # top the bases up (one STATUS
        mv      t6, ra                  # snapshot, t2; refill_both returns
        j       refill_both             # to the poll)
ext_start:
        # An EXT descriptor the hardware took. GEN_OK goes FIRST: the
        # descriptor cannot complete before its bases-done bits, which
        # ext_init writes after it, so a GEN_OK can never land on the next
        # descriptor (it would skip that one's set-up).
        li      t3, CMD_GEN_OK
        sw      t3, W_CMD(a0)
        mv      s3, ra                  # ext_init returns to the poll
        j       ext_init

row_complete:
        BIT     t3, t2, B_ARMED         # armed: the hardware leaves COMPLETE
        bnez    t3, h_ret               # itself next cycle; never unarmed
        j       fw_fault

row_idle:
        BIT     t4, t2, B_ENABLE
        beqz    t4, h_ret
row_next:
        BIT     t4, t2, B_STAGED        # staged: the hardware takes it
        bnez    t4, h_ret
        BIT     t4, t2, B_HEAD
        beqz    t4, h_ret
        srli    t4, t2, B_DECLINED      # judged bad (bit 31: no mask)
        bnez    t4, fetch_start
judge_head:                             # an open head the poll did not see
        lw      t3, R_HEAD_SUM(a0)
        JUDGE
        ret
fetch_start:                            # take the declined head: the normal
        li      t4, ST_FETCH            # path takes it to CH_ERROR
        sw      t4, W_CMD(a0)
        ret

row_fetch:
        BIT     t4, t2, B_TILE_BAD
        bnez    t4, fetch_error
        BIT     t4, t2, B_PENDING
        bnez    t4, h_ret
        BIT     t4, t2, B_VALID         # the firmware takes only a head it
        bnez    t4, fw_fault            # declined, so never a valid one
fetch_error:
        li      t3, ST_ERROR
        sw      t3, W_CMD(a0)
h_ret:
        ret

# fw_fault: a state this policy never creates -- a descriptor taken unarmed
# (in XFER_DATA or COMPLETE) or a valid one the firmware took itself (every
# valid head is staged armed, and the firmware takes only heads it
# declined). Say so and stop the channel rather than guess: a firmware error
# packet carrying STATUS, then CH_ERROR (legal from FETCH_DESC, XFER_DATA
# and COMPLETE). A channel reset recovers it.
fw_fault:
        sw      t2, W_FW_ERROR(a0)
        li      t3, ST_ERROR
        sw      t3, W_CMD(a0)
        ret

# ext_init (link s3): set up the run-base generator of each enabled
# direction for the latched EXT descriptor and prefill its FIFO. Reads the
# totals back from the window. Clobbers what gen_init and refill_both do.
ext_init:
        sw      s3, SCR_LINK(a1)
        lw      t2, R_STATUS(a0)
        lw      a6, R_CFG(a0)
        BIT     t3, a6, C_EN_READ
        beqz    t3, 1f
        mv      a2, a1
        addi    a3, a0, R_SRC_LO
        addi    a4, a0, R_EXT0
        BIT     a5, t2, B_RD_PER_BEAT
        lw      s9, R_RD_TOTAL(a0)
        jal     t6, gen_init
1:      BIT     t3, a6, C_EN_WRITE
        beqz    t3, 2f
        addi    a2, a1, WR_BLOCK
        addi    a3, a0, R_DST_LO
        addi    a4, a0, R_EXT0 + 12
        BIT     a5, t2, B_WR_PER_BEAT
        lw      s9, R_WR_TOTAL(a0)
        jal     t6, gen_init
2:      jal     t6, refill_both
        lw      s3, SCR_LINK(a1)
        jr      s3

# refill_both (link t6): top up each enabled direction not yet done.
# Needs t2 = STATUS.  Clobbers everything refill does, s3 and t2.
# Both directions are judged on that ONE snapshot. Re-reading STATUS between
# them would be wrong: once the first direction's last "done" is written the
# hardware may complete this descriptor and take the next, and a fresh STATUS
# would then describe the next descriptor -- this one's leftover generator
# would mark the next one's bases done. While the snapshot says a direction is
# not done, the descriptor cannot complete, so acting on it is always safe.
refill_both:
        mv      s3, t6
        sw      t2, SCR_STATUS(a1)
        lw      a6, R_CFG(a0)
        BIT     t3, a6, C_EN_READ
        beqz    t3, 1f
        BIT     t3, t2, B_RD_DONE
        bnez    t3, 1f
        mv      a2, a1
        addi    a3, a0, W_RD_BASE_LO
        li      a4, CMD_RD_DONE
        li      a5, 0
        jal     t6, refill
1:      lw      a6, R_CFG(a0)
        lw      t2, SCR_STATUS(a1)      # the snapshot (refill used t2)
        BIT     t3, a6, C_EN_WRITE
        beqz    t3, 2f
        BIT     t3, t2, B_WR_DONE
        bnez    t3, 2f
        addi    a2, a1, WR_BLOCK
        addi    a3, a0, W_WR_BASE_LO
        li      a4, CMD_WR_DONE
        li      a5, 4
        jal     t6, refill
2:      jr      s3

# gen_init (link t6): a2 = generator block, a3 = &base (window, LO then HI),
# a4 = &stride_0 (window; stride_1, then {wrap1, wrap0, inner} follow),
# a5 = per-beat, s9 = total beats.  Clobbers t1, t3-t5, gp.
# Positions follow stream_run_addr_gen's start: run 0 / beat 0 is the
# descriptor's own address, so the first base is position 1.
gen_init:
        lw      t1, 0(a3)
        sw      t1, G_BASE_LO(a2)
        lw      t1, 4(a3)
        sw      t1, G_BASE_HI(a2)
        lw      t1, 0(a4)
        sw      t1, G_S0_LO(a2)
        srai    t3, t1, 31
        sw      t3, G_S0_HI(a2)
        lw      t1, 4(a4)
        sw      t1, G_S1_LO(a2)
        srai    t3, t1, 31
        sw      t3, G_S1_HI(a2)
        lw      t1, 8(a4)
        slli    t3, t1, 16
        srli    t3, t3, 16              # inner_count, 0 means 1
        bnez    t3, 1f
        li      t3, 1
1:      sw      t3, G_INNER(a2)
        srli    t4, t1, 16
        andi    t4, t4, 0x3f
        MASK    t4, G_M0_LO
        srli    t4, t1, 22
        andi    t4, t4, 0x3f
        MASK    t4, G_M1_LO
        sw      s9, G_TOTAL(a2)
        sw      a5, G_PER_BEAT(a2)
        lw      t1, R_ALG(a0)           # the next-address selector: 0 is
        bnez    t1, gen_init_z          # stream_run_addr_gen's, below
        sw      zero, G_ACC0_LO(a2)
        sw      zero, G_ACC0_HI(a2)
        beqz    a5, 3f
        li      t1, 1                   # per beat: beat 0 covered, step 1
        sw      t1, G_GEN(a2)
        sw      t1, G_STEP(a2)
        bleu    t3, t1, 2f
        sw      t1, G_I0(a2)            # (i0, i1) = (1, 0)
        sw      zero, G_I1(a2)
        lw      t1, G_S0_LO(a2)
        sw      t1, G_ACC0_LO(a2)
        lw      t1, G_S0_HI(a2)
        sw      t1, G_ACC0_HI(a2)
        sw      zero, G_ACC1_LO(a2)
        sw      zero, G_ACC1_HI(a2)
        j       gi_tail
3:      sw      t3, G_GEN(a2)           # runs: run 0 covered, step inner
        sw      t3, G_STEP(a2)
2:      sw      zero, G_I0(a2)          # (i0, i1) = (0, 1)
        li      t1, 1
        sw      t1, G_I1(a2)
        lw      t1, G_S1_LO(a2)
        sw      t1, G_ACC1_LO(a2)
        lw      t1, G_S1_HI(a2)
        sw      t1, G_ACC1_HI(a2)
gi_tail:
        # No wrap on either dimension: keep the addresses themselves, so a
        # base is one 64-bit add (refill's fast path). cur = base + acc0 +
        # acc1 is the next base, row = base + acc1 the start of its row.
        lw      t1, 8(a4)
        slli    t1, t1, 4
        srli    t1, t1, 20              # {wrap1, wrap0}, bits [27:16]
        seqz    t1, t1
        sw      t1, G_NOWRAP(a2)
        beqz    t1, 9f
        lw      t1, G_BASE_LO(a2)
        lw      t3, G_BASE_HI(a2)
        lw      t4, G_ACC1_LO(a2)
        lw      t5, G_ACC1_HI(a2)
        add     t4, t1, t4              # row = base + acc1
        sltu    gp, t4, t1
        add     t5, t3, t5
        add     t5, t5, gp
        sw      t4, G_ACC1_LO(a2)
        sw      t5, G_ACC1_HI(a2)
        lw      t1, G_ACC0_LO(a2)
        lw      t3, G_ACC0_HI(a2)
        add     t1, t4, t1              # cur = row + acc0
        sltu    gp, t1, t4
        add     t3, t5, t3
        add     t3, t3, gp
        sw      t1, G_ACC0_LO(a2)
        sw      t3, G_ACC0_HI(a2)
9:      jr      t6

# refill (link t6): a2 = generator block, a3 = &BASE_LO (window), a4 = the
# CMD done bit, a5 = shift of this direction's count in FIFO.  Pushes bases
# until the FIFO is full or every base is out, then saves the position.
# Clobbers t1-t5, gp, tp, s4-s11, a5-a7.
refill:
        lw      t1, R_FIFO(a0)
        srl     t1, t1, a5
        andi    t1, t1, 7
        li      t3, 4
        sub     gp, t3, t1              # free entries (only we push)
        lw      t1, G_NOWRAP(a2)
        bgtz    t1, refill_fast
        bltz    t1, refill_z
        lw      s4, G_BASE_LO(a2)
        lw      a5, G_BASE_HI(a2)
        lw      s5, G_ACC0_LO(a2)
        lw      s6, G_ACC0_HI(a2)
        lw      s7, G_ACC1_LO(a2)
        lw      s8, G_ACC1_HI(a2)
        lw      s9, G_I0(a2)
        lw      s10, G_I1(a2)
        lw      s11, G_GEN(a2)
        lw      tp, G_TOTAL(a2)
        lw      a6, G_STEP(a2)
        lw      a7, G_PER_BEAT(a2)
r_loop:
        bgeu    s11, tp, r_done         # every base is out
        blez    gp, r_save              # FIFO full
        lw      t1, G_M0_LO(a2)         # base + (acc0 & m0) + (acc1 & m1)
        and     t1, t1, s5
        lw      t3, G_M0_HI(a2)
        and     t3, t3, s6
        add     t4, s4, t1
        sltu    t5, t4, t1
        add     t1, a5, t3
        add     t1, t1, t5
        lw      t3, G_M1_LO(a2)
        and     t3, t3, s7
        add     t4, t4, t3
        sltu    t5, t4, t3
        add     t1, t1, t5
        lw      t3, G_M1_HI(a2)
        and     t3, t3, s8
        add     t1, t1, t3
        sw      t4, 0(a3)               # BASE_LO
        sw      t1, 4(a3)               # BASE_HI pushes
        addi    gp, gp, -1
        add     s11, s11, a6            # gen += step
        beqz    a7, r_next_run
        lw      t1, G_INNER(a2)         # per beat: i0 fastest
        addi    t1, t1, -1
        beq     s9, t1, r_next_row
        addi    s9, s9, 1
        lw      t1, G_S0_LO(a2)
        lw      t3, G_S0_HI(a2)
        add     s5, s5, t1
        sltu    t5, s5, t1
        add     s6, s6, t3
        add     s6, s6, t5
        j       r_loop
r_next_row:
        li      s9, 0
        li      s5, 0
        li      s6, 0
r_next_run:
        addi    s10, s10, 1             # i1 is a 16-bit index, as in RTL
        slli    s10, s10, 16
        srli    s10, s10, 16
        beqz    s10, r_wrap
        lw      t1, G_S1_LO(a2)
        lw      t3, G_S1_HI(a2)
        add     s7, s7, t1
        sltu    t5, s7, t1
        add     s8, s8, t3
        add     s8, s8, t5
        j       r_loop
r_wrap:
        li      s7, 0
        li      s8, 0
        j       r_loop
r_done:
        sw      a4, W_CMD(a0)           # bases done (no state change)
r_save:
        sw      s5, G_ACC0_LO(a2)
        sw      s6, G_ACC0_HI(a2)
        sw      s7, G_ACC1_LO(a2)
        sw      s8, G_ACC1_HI(a2)
        sw      s9, G_I0(a2)
        sw      s10, G_I1(a2)
        sw      s11, G_GEN(a2)
        jr      t6

# The no-wrap fast path: cur (s5:s6) is the next base, row (s7:s8) its row's
# start; a base is a push and one 64-bit add. Same positions, same 16-bit i1
# wrap (row returns to the descriptor's base), as the masked path.
refill_fast:
        lw      s5, G_ACC0_LO(a2)
        lw      s6, G_ACC0_HI(a2)
        lw      s7, G_ACC1_LO(a2)
        lw      s8, G_ACC1_HI(a2)
        lw      s4, G_S0_LO(a2)
        lw      a5, G_S0_HI(a2)
        lw      t2, G_S1_LO(a2)
        lw      t4, G_S1_HI(a2)
        lw      s9, G_I0(a2)
        lw      s10, G_I1(a2)
        lw      s11, G_GEN(a2)
        lw      tp, G_TOTAL(a2)
        lw      a6, G_STEP(a2)
        lw      a7, G_PER_BEAT(a2)
        lw      t3, G_INNER(a2)
        addi    t3, t3, -1              # last i0 of a row
f_loop:
        bgeu    s11, tp, r_done         # every base is out
        blez    gp, r_save              # FIFO full
        sw      s5, 0(a3)               # BASE_LO
        sw      s6, 4(a3)               # BASE_HI pushes
        addi    gp, gp, -1
        add     s11, s11, a6
        beqz    a7, f_row               # runs: every base starts a row
        beq     s9, t3, f_row_pb
        addi    s9, s9, 1               # per beat, along the row: cur += s0
        add     s5, s5, s4
        sltu    t5, s5, s4
        add     s6, s6, a5
        add     s6, s6, t5
        j       f_loop
f_row_pb:
        li      s9, 0
f_row:
        addi    s10, s10, 1             # next row: row += s1, cur = row
        slli    s10, s10, 16
        srli    s10, s10, 16
        beqz    s10, f_wrap
        add     s7, s7, t2
        sltu    t5, s7, t2
        add     s8, s8, t4
        add     s8, s8, t5
        mv      s5, s7
        mv      s6, s8
        j       f_loop
f_wrap:
        lw      s7, G_BASE_LO(a2)       # i1 wrapped: offset_1 is 0 again
        lw      s8, G_BASE_HI(a2)
        mv      s5, s7
        mv      s6, s8
        j       f_loop

# Selector 1, Z-order (rapids TASK-035). The unit is a beat (per beat) or a
# run of inner_count beats (stride_0 == the beat size); unit k sits at
#   base + ((x * S0) & m0) + ((y * s1) & m1),
# x the even bits of k, y the odd bits (Morton order), S0 = stride_0 per
# beat or inner_count beats (inner_count << OFF_W) per run. Unit 0 is the
# descriptor's own address, so the first base is k = 1 (x = 1, y = 0).
# gen_init_z (from gen_init, link t6): t3 = inner_count, a5 = per-beat,
# a6 = CFG, the masks, strides, total and per-beat flag already stored.
gen_init_z:
        bnez    a5, 1f
        srli    t1, a6, 16              # runs: S0 = inner_count << OFF_W
        andi    t1, t1, 0xf
        sll     t4, t3, t1
        sw      t4, G_S0_LO(a2)
        sw      zero, G_S0_HI(a2)
        j       2f
1:      li      t3, 1                   # per beat: the unit is one beat
2:      sw      t3, G_GEN(a2)           # unit 0 covered
        sw      t3, G_STEP(a2)
        li      t1, 1
        sw      t1, G_I0(a2)            # k = 1
        lw      t1, G_S0_LO(a2)         # x * S0 = S0, y * s1 = 0
        sw      t1, G_ACC0_LO(a2)
        lw      t1, G_S0_HI(a2)
        sw      t1, G_ACC0_HI(a2)
        sw      zero, G_ACC1_LO(a2)
        sw      zero, G_ACC1_HI(a2)
        li      t1, -1
        sw      t1, G_NOWRAP(a2)
        jr      t6

# refill_z (from refill, gp = free entries): as the masked path, but the
# position steps in Morton order. k -> k + 1 clears k's trailing ones and
# sets the bit above them; bit 2i is x's bit i, bit 2i+1 is y's, so each
# cleared bit subtracts (S0 or s1) << i and the set bit adds it -- no
# multiplier, about two bits a step on average.
refill_z:
        lw      s4, G_BASE_LO(a2)
        lw      a5, G_BASE_HI(a2)
        lw      s5, G_ACC0_LO(a2)       # x * S0
        lw      s6, G_ACC0_HI(a2)
        lw      s7, G_ACC1_LO(a2)       # y * s1
        lw      s8, G_ACC1_HI(a2)
        lw      s9, G_I0(a2)            # k
        lw      s11, G_GEN(a2)
        lw      tp, G_TOTAL(a2)
        lw      a6, G_STEP(a2)
z_loop:
        bgeu    s11, tp, r_done         # every base is out
        blez    gp, r_save              # FIFO full
        lw      t1, G_M0_LO(a2)         # base + (accx & m0) + (accy & m1)
        and     t1, t1, s5
        lw      t3, G_M0_HI(a2)
        and     t3, t3, s6
        add     t4, s4, t1
        sltu    t5, t4, t1
        add     t1, a5, t3
        add     t1, t1, t5
        lw      t3, G_M1_LO(a2)
        and     t3, t3, s7
        add     t4, t4, t3
        sltu    t5, t4, t3
        add     t1, t1, t5
        lw      t3, G_M1_HI(a2)
        and     t3, t3, s8
        add     t1, t1, t3
        sw      t4, 0(a3)               # BASE_LO
        sw      t1, 4(a3)               # BASE_HI pushes
        addi    gp, gp, -1
        add     s11, s11, a6            # gen += step
        mv      a7, s9                  # k's bits, lowest first
        lw      t2, G_S0_LO(a2)         # S0 << i
        lw      s10, G_S0_HI(a2)
        lw      t3, G_S1_LO(a2)         # s1 << i
        lw      t4, G_S1_HI(a2)
z_bit:
        andi    t1, a7, 1               # x's bit i
        beqz    t1, z_xset
        sltu    t5, s5, t2              # set: clear it, accx -= S0 << i
        sub     s5, s5, t2
        sub     s6, s6, s10
        sub     s6, s6, t5
        srli    a7, a7, 1
        andi    t1, a7, 1               # y's bit i
        beqz    t1, z_yset
        sltu    t5, s7, t3              # set: clear it, accy -= s1 << i
        sub     s7, s7, t3
        sub     s8, s8, t4
        sub     s8, s8, t5
        srli    a7, a7, 1
        srli    t1, t2, 31              # next i: both strides << 1
        slli    s10, s10, 1
        or      s10, s10, t1
        slli    t2, t2, 1
        srli    t1, t3, 31
        slli    t4, t4, 1
        or      t4, t4, t1
        slli    t3, t3, 1
        j       z_bit
z_xset:
        add     s5, s5, t2              # accx += S0 << i
        sltu    t5, s5, t2
        add     s6, s6, s10
        add     s6, s6, t5
        j       z_next
z_yset:
        add     s7, s7, t3              # accy += s1 << i
        sltu    t5, s7, t3
        add     s8, s8, t4
        add     s8, s8, t5
z_next:
        addi    s9, s9, 1
        j       z_loop
