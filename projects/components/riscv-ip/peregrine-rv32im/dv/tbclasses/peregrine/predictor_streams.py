# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: predictor_streams
# Purpose: The PRD §5 predictor stress streams for peregrine_core, as
#          self-checking RV32IM programs: loops of every trip count 1-4,
#          BTB and BHT aliasing pairs, JALR target changes, mispredicts in
#          the same cycle as an ID interlock, and a stale BTB entry after
#          code is rewritten.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""Predictor stress streams.

Each stream is a complete program: it computes into s0, compares s0 with the
value the generator expects, and stores 1 to ``tohost`` on a match (3 on a
mismatch, 5 on an unexpected trap).  The trap handler services ``ecall``
(returns to mepc + 4); any other trap fails the program.  Aliasing pairs are placed with
``.balign``; ``alias_symbols`` names the labels the test checks after
linking, so a layout change cannot silently stop the pair from aliasing.
"""

from dataclasses import dataclass, field

BTB_ENTRIES = 32
BHT_ENTRIES = 256


@dataclass(frozen=True)
class Stream:
    name: str
    body: str                     # text section, after the prologue
    expected: int                 # final s0
    data: str = ""                # extra .data lines
    alias_symbols: tuple = ()     # (label_a, label_b, "btb" | "bht")
    notes: str = ""


@dataclass
class StreamSet:
    streams: list = field(default_factory=list)


PROLOGUE = """\
.section .text
.globl _start
_start:
    la t0, trap_handler
    csrw mtvec, t0
    li s0, 0
"""

EPILOGUE = """\
check:
    li t4, {expected:#x}
    li x31, 3
    bne s0, t4, finish
    li x31, 1
finish:
    la t0, tohost
    sw x31, 0(t0)
1:  j 1b
trap_handler:
    csrrw x31, mscratch, x31
    csrr x31, mcause
    addi x31, x31, -11
    bnez x31, trap_fail
    csrr x31, mepc
    addi x31, x31, 4
    csrw mepc, x31
    csrrw x31, mscratch, x31
    mret
trap_fail:
    li x31, 5
    j finish
"""

DATA = """\
.section .data
.align 3
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
.align 2
data: .word 7, 0, 0, 0
"""


def program(stream: Stream) -> str:
    return (PROLOGUE + stream.body + "\n    j check\n" +
            EPILOGUE.format(expected=stream.expected) + DATA + stream.data)


def loop_trip(n: int, reps: int) -> Stream:
    """An inner loop of trip count ``n`` (back edge taken n-1 times, then not
    taken), run ``reps`` times: the 1-bit/2-bit contrast."""
    body = f"""\
    li s1, {reps}
1:  li t0, {n}
2:  addi s0, s0, 1
    addi t0, t0, -1
    bnez t0, 2b
    addi s1, s1, -1
    bnez s1, 1b
"""
    return Stream(f"loop_trip{n}", body, n * reps,
                  notes="inner back edge taken n-1 of n times")


def btb_alias(reps: int) -> Stream:
    """Two always-taken branches with the same BTB index and different tags
    (and different BHT indexes): each evicts the other's entry."""
    body = f"""\
    li s1, {reps}
    li t1, 1
3:  jal ra, fa
    jal ra, fb
    addi s1, s1, -1
    bnez s1, 3b
    j check
.balign 1024
fa: bnez t1, 4f
    addi s0, s0, 100
4:  addi s0, s0, 1
    ret
.balign 1024
.skip 128
fb: bnez t1, 5f
    addi s0, s0, 100
5:  addi s0, s0, 1
    ret
"""
    return Stream("btb_alias", body, 2 * reps, alias_symbols=("fa", "fb", "btb"),
                  notes="same BTB index, different tag, different BHT index")


def bht_alias(reps: int) -> Stream:
    """An always-taken and a never-taken branch sharing one BHT counter (and
    one BTB index): the never-taken one drags the shared counter down.  The
    pair sits at BHT index 128 (1 KiB-aligned + 512 B), which no other
    stream uses, so a counter left by an earlier program cannot hide the
    interference."""
    body = f"""\
    li s1, {reps}
    li t1, 1
3:  jal ra, ga
    jal ra, gb
    addi s1, s1, -1
    bnez s1, 3b
    j check
.balign 1024
.skip 512
ga: bnez t1, 4f
    addi s0, s0, 100
4:  addi s0, s0, 1
    ret
.balign 1024
.skip 512
gb: bnez x0, 5f
    addi s0, s0, 1
5:  ret
"""
    return Stream("bht_alias", body, 2 * reps, alias_symbols=("ga", "gb", "bht"),
                  notes="same BHT counter, opposite directions")


def jalr_targets(reps: int) -> Stream:
    """An indirect call whose target cycles through three functions, and a
    helper called from two sites, so its return target alternates (no RAS)."""
    body = f"""\
    la a1, ftable
    li s1, {reps}
    li t3, 0
3:  slli t4, t3, 2
    add t4, a1, t4
    lw t2, 0(t4)
    jalr ra, 0(t2)
    addi t3, t3, 1
    li t5, 3
    bne t3, t5, 4f
    li t3, 0
4:  jal ra, helper
    jal ra, helper
    addi s1, s1, -1
    bnez s1, 3b
    j check
f0: addi s0, s0, 1
    ret
f1: addi s0, s0, 2
    ret
f2: addi s0, s0, 3
    ret
helper:
    addi s0, s0, 10
    ret
"""
    expected = sum((i % 3) + 1 for i in range(reps)) + 20 * reps
    data = "ftable: .word f0, f1, f2\n"
    return Stream("jalr_targets", body, expected, data=data,
                  notes="indirect target changes every call; return target alternates")


def interlock(reps: int) -> Stream:
    """A branch that alternates direction (so it mispredicts often), each
    time with an ID-stage interlock on the wrong path: load-to-branch, CSR
    serialization, a load-use pair, and an M result feeding the branch."""
    body = f"""\
    la a0, data
    li t5, 7
    li t1, 0
    li s1, {reps}
3:  xori t1, t1, 1
    lw a2, 0(a0)
    bnez t1, 4f
    beq a2, x0, check
    addi s0, s0, 1
4:  csrr t2, mscratch
    bnez t1, 5f
    csrr t3, mscratch
    addi s0, s0, 2
5:  bnez t1, 6f
    lw a3, 0(a0)
    add a4, a3, a3
    add s0, s0, a4
6:  mul a5, t1, t5
    bnez a5, 7f
    addi s0, s0, 3
7:  addi s1, s1, -1
    bnez s1, 3b
"""
    # t1 runs 1, 0, 1, 0, ...: every even-numbered pass (t1 = 0) adds
    # 1 + 2 + 14 + 3.
    return Stream("interlock", body, 20 * (reps // 2),
                  notes="mispredict with load-to-branch, CSR, load-use, M on the wrong path")


def stale_entry() -> Stream:
    """A taken jump installs a BTB entry, then the program rewrites the jump
    into an M instruction (with fence.i): the next pass fetches it with a
    stale taken prediction, mispredicts once and clears the entry; the pass
    after predicts nothing.  The stale mispredict lands on an instruction
    that holds in EX for the M unit, and its result feeds the check: a
    redirect issued during the hold would flush it out of ID/EX."""
    body = """\
    li s0, 1
    li a6, 3
    li s1, 3
3:  jal ra, site
    la t0, site_br
    la t3, patch_src
    lw t2, 0(t3)
    sw t2, 0(t0)
    fence.i
    nop
    nop
    nop
    addi s1, s1, -1
    bnez s1, 3b
    j check
site:
site_br:
    j 4f
    addi s0, s0, 1
4:  ret
patch_src:
    mul s0, s0, a6
"""
    # Pass 1 jumps over the add (s0 = 1); passes 2 and 3 run the mul and
    # the add: 1 * 3 + 1 = 4, then 4 * 3 + 1 = 13.
    return Stream("stale_entry", body, 13, alias_symbols=(),
                  notes="pass 2 mispredicts on a stale entry at an M instruction")


def trap_shadow(reps: int) -> Stream:
    """An ecall directly followed by a branch: the ecall traps in MEM while
    the branch is in EX, killing it; it re-executes after the handler.  The
    killed pass must not write the predictor, or the counter takes two steps
    per pass.

    The direction runs T, T, N, N (bit 1 of the loop count).  The killed
    copy's update lands just before the re-executed copy is looked up, so a
    double step shows only when the same direction repeats while the
    counter is still moving.  A strictly alternating branch hid it: both
    counters re-converge at 00 every not-taken pass (measured: the mutant
    survived the alternating version once the install value became 01)."""
    body = f"""\
    li s1, {reps}
3:  srli t1, s1, 1
    andi t1, t1, 1
    ecall
    bnez t1, 4f
    addi s0, s0, 1
4:  addi s1, s1, -1
    bnez s1, 3b
"""
    expected = sum(1 for n in range(1, reps + 1) if not (n >> 1) & 1)
    return Stream("trap_shadow", body, expected,
                  notes="a branch killed in EX by an older trap, then re-executed")


def streams(level: str) -> list:
    reps = {"gate": 8, "func": 40, "full": 200}[level]
    return ([loop_trip(n, reps) for n in (1, 2, 3, 4)] +
            [btb_alias(reps), bht_alias(reps), jalr_targets(reps),
             interlock(2 * reps), stale_entry(), trap_shadow(2 * reps)])


def check_alias(kind: str, a: int, b: int) -> None:
    """Raise unless addresses a and b alias as the stream intends."""
    btb_a, btb_b = (a >> 2) % BTB_ENTRIES, (b >> 2) % BTB_ENTRIES
    bht_a, bht_b = (a >> 2) % BHT_ENTRIES, (b >> 2) % BHT_ENTRIES
    tag_a, tag_b = a >> 7, b >> 7
    assert btb_a == btb_b and tag_a != tag_b, \
        f"0x{a:x}/0x{b:x}: not a BTB conflict (index {btb_a}/{btb_b})"
    if kind == "btb":
        assert bht_a != bht_b, f"0x{a:x}/0x{b:x}: share a BHT counter too"
    else:
        assert bht_a == bht_b, f"0x{a:x}/0x{b:x}: do not share a BHT counter"
