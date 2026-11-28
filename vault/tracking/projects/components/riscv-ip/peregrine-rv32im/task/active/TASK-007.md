# TASK-007: interruptible M instructions -- cancel in flight, one instruction of progress after mret

**Priority:** P3
**Status:** active 2026-11-27 (filed 2026-11-27; owner: "yes"; started after TASK-005 landed, owner "start 7").
**Owner:** Claude
**From:** [ISSUE-001](../../issue/closed/ISSUE-001.md), option 2 with a progress guarantee

## Why

An M instruction can't be interrupted today: a pending interrupt waits for
every M instruction ahead of it, about 34 cycles each. Cancelling on its
own is not enough. The first stage-2 build cancelled and restarted, and
livelocked when interrupts arrived faster than the divider finished
(`test_peregrine_mext`, mutant M5).

## What

- **Take the interrupt while an M instruction holds in EX.** Cancel the M
  unit and discard its result; `mepc` is the M instruction's own PC.
- **Progress rule:** the first instruction after an `mret` cannot be
  interrupted until it retires. One flag: set by `mret`, cleared when the
  next instruction retires or takes a synchronous trap. Every interrupt
  return then retires at least one instruction, so a cancelled M
  instruction completes on its second issue, whatever the interrupt rate.
- **Worst-case latency is one M instruction** (about 34 cycles), and only
  when an interrupt arrives right after an `mret` into one. Today it is
  about 34 cycles per back-to-back M instruction.

## Done when

- `test_peregrine_mext`'s re-raise case retires every M instruction.
- A new directed test of k back-to-back divides under interrupts measures
  the latency bound, and the bound is written into PRD §4.3/§4.4.
- Mutants:
  - with the progress flag dropped, the suite livelocks (times out);
  - with the cancel dropped, it shows the old latency.
- riscv-formal, the shadow CSR model and spike lockstep agree: `mepc`
  points at the M instruction.
- 75 MHz still closes, measured in both `MUL_DSP` builds.
- peregrine FULL is green from clean.
- The HAS/MAS trap chapters are updated, at their current revision.
