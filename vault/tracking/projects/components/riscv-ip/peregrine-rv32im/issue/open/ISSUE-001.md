# ISSUE-001: M instructions are not interruptible -- interrupt latency vs forward progress

**Priority:** P3
**Status:** open 2026-11-24 -- the simple solution is built and accepted for
now (owner, 2026-11-24: "do the simple solution first; we can reevaluate
later. add an issue to track it"); reevaluate before the book's interrupt
chapter or when interrupt latency is measured.
**Owner:** TBD
**Filed:** 2026-11-24
**Related:** riscv-ip/peregrine-rv32im TASK-001 stage 2 (d38f0b7ef); PRD §4.3,
§4.4; handbook design/interrupts-must-not-discard-finished-work

## What we have

peregrine samples interrupts at MEM. An M instruction holds in EX for up to
33 stall cycles (hold-in-EX, PRD P3) and reaches MEM only with its result
done. Since stage 2 it is **not interruptible there**: a pending interrupt
is taken on the next instruction (`mem_irq` gated by `~ex_mem_q.m_op` in
`peregrine_core.sv`). That is precise -- `mepc` is the successor's PC.

## Why it was done

The first stage-2 build let the interrupt take the finished M instruction.
Its result was discarded and it restarted after `mret`. With the timer
re-raised 3 to 40 cycles after each acknowledge (`test_peregrine_mext`), the
M instruction was caught every time and never retired: a livelock. Mutant M5
(the gate removed) reproduces it as a timeout.

## What it costs

Interrupt latency. A pending interrupt waits for every M instruction ahead of
it to finish: about 34 cycles each, so a run of k back-to-back M
instructions adds about 34k cycles. A loop body of only M instructions and a
branch takes the interrupt at the branch. Not yet measured as a worst case.

## Options to reevaluate

1. **Keep it** (current). Bounded latency, guaranteed forward progress, no
   extra hardware. Write the bound into the PRD's interrupt-latency figure.
2. **Interrupt at start, cancel the unit.** Take the interrupt on the M
   instruction in its first EX cycle and cancel the unit. Cuts latency to
   about a normal instruction's, but the livelock returns whenever the
   interrupt period is shorter than the unit's latency; needs a progress
   guarantee on top (for example, at most one cancel per M instruction).
3. **Interrupt mid-flight with a saved partial result.** Lowest latency and
   forward progress, at the cost of architectural state (or a restartable
   iteration count) the spec does not have. Probably out of scope for a
   teaching core.
4. **Bound it at the source.** Leave the core as is and document a minimum
   interrupt period for software. Weakest: a level-triggered device line is
   not software-controlled.

## Resolves into

A recorded decision: keep (close with the latency bound in the PRD), or a
task to build option 2 or 3. Either way, add the worst-case interrupt
latency to the measurement set (a directed test with k back-to-back M
instructions).
