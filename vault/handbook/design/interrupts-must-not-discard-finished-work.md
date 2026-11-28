---
title: Interrupts must not discard finished work
summary: A commit-point interrupt that throws away a multi-cycle instruction's completed result can starve that instruction forever when interrupts arrive faster than its latency. Make a long instruction non-interruptible once its work is done, and take the interrupt on the next instruction; it stays precise (peregrine M unit, 2026-11-23). Cancelling it mid-run is safe only with a progress rule: the first instruction after an interrupt return is not interruptible (peregrine TASK-007, 2026-11-27).
---

# Interrupts must not discard finished work

**An in-order core that samples interrupts at its commit point, and lets an
interrupt take an instruction whose work is already done, has no
forward-progress guarantee for its longest instruction.**

## The failure

peregrine (riscv-ip peregrine-rv32im TASK-001 stage 2) holds an M
instruction in EX for 33 cycles while the iterative unit runs, then lets
it move to MEM, where interrupts are sampled. The first build treated it
like any other instruction: a pending interrupt attached to it, it trapped
instead of committing, and its result was discarded. After `mret` it
started again from zero.

The directed suite re-raised the machine timer 3 to 40 cycles after each
acknowledge. Most of those delays are shorter than the M instruction's
time from `mret` to MEM, so the interrupt was pending again every time it
arrived. The M instruction never retired, and the run timed out in the
handler. A level-triggered device line that re-asserts quickly does the
same thing in a real system.

## The rule

- **Once a long instruction's work is done, it commits.** An interrupt
  pending when it reaches the commit point is taken on the next
  instruction.
- **That is still precise.** The interrupt boundary falls between the long
  instruction and its successor, and `mepc` is the successor's PC.
  Everything older has committed, and nothing younger has touched state.
- **Price it.** The interrupt latency grows by the long instruction's
  latency. A run of back-to-back M instructions delays an interrupt by
  about 34 cycles each. State the bound in the spec; it belongs to the
  book's interrupt-latency table.

Interrupting the long instruction while it runs, and cancelling the unit,
cuts the latency, but on its own it keeps the livelock whenever the
interrupt period is shorter than the instruction. It needs a progress
rule too: **the first instruction after an interrupt return cannot be
interrupted until it commits.** Every return then retires one
instruction, so a cancelled instruction completes on its second issue.
peregrine does both (TASK-007, 2026-11-27): an M instruction still running
in EX is interrupted with `mepc` = its own PC, a finished one still
commits, and an `mret` sets a flag that holds the interrupt decision low
until the next commit. The worst-case latency falls from one M instruction
per back-to-back M instruction to one in total (measured: 271 cycles
behind 8 divides before, 38 after). With the flag removed, the same fast
timer livelocks it again.

## How to find it

Raise interrupts faster than the longest instruction's latency, and assert
that every interrupted instruction executes later
([[precise-trap-checks]]). A source slower than the unit never asks the
question.

## Related

- [[precise-trap-checks]]: the DV method, including the stale-result trap
  a re-executed instruction hides.
