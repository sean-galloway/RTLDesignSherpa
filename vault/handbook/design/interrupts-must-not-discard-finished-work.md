---
title: Interrupts must not discard finished work
summary: A commit-point interrupt that throws away a multi-cycle instruction's completed result can starve that instruction forever when interrupts arrive faster than its latency. Make a long instruction non-interruptible once its work is done, and take the interrupt on the next instruction; it stays precise (peregrine M unit, 2026-11-23).
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

The alternative, interrupting the long instruction early (at its start)
and cancelling the unit, cuts the latency but keeps the livelock whenever
the interrupt period is shorter than the instruction.

## How to find it

Raise interrupts faster than the longest instruction's latency, and assert
that every interrupted instruction executes later
([[precise-trap-checks]]). A source slower than the unit never asks the
question.

## Related

- [[precise-trap-checks]]: the DV method, including the stale-result trap
  a re-executed instruction hides.
