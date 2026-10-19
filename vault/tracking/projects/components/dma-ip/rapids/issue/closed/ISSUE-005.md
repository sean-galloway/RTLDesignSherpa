# ISSUE-005: scheduler and descriptor-engine completion packets ignore SCHED_CONFIG.COMPL_EN

**Priority:** Low -- observability only; nothing functional depends on it.
**Status:** CLOSED 2026-09-29 -- decided: the bit gates (closing note at the end). Was: OPEN 2026-09-28. Surfaced by the rapids TASK-015 top-level monitor
test, which clears the SRC `RDMON_PKT_MASK` the monbus group filters on: with
`SCHED_CONFIG` programmed `SCHED_EN=1, ERR_EN=1` (COMPL_EN = 0) the capture
trace still carried a Completion from the descriptor engine (agent 0x11/0x12)
and two from the scheduler (agent 0x31/0x32) for every transfer.

## What is known

`scheduler_group_beats.sv` line ~340 documents `cfg_sched_compl_enable` as
"(always enabled)": the input exists on the group and the array but does not
gate the emitter. The descriptor engine's fetch-complete packet has no enable at
all. With the reset `PKT_MASK` (all masked) the group drops these packets, so
the bit looks honoured until a host unmasks the completion class.

## Why an issue, not a bug

The intended behaviour is not written down: either the register bit should gate
these emitters (then it is a bug against the HAS `SCHED_CONFIG` description), or
completion packets are meant to be always-on and filtered only at the group
(then the register description and the config-block mapping should say so and
the bit retired). Decide, then file the bug or the doc fix.

---

**CLOSED 2026-09-29. Decision: `SCHED_CONFIG.COMPL_EN` gates the CORE
Completion packets.** The bit was already plumbed from the register through
the top, core, array and group, every sibling monitor honours its own
`COMPL_EN`, and its reset value is 1 -- so honouring it changes nothing for a
host that never writes it, and a register bit that does nothing was the worse
outcome.

Where: `scheduler_group_beats.sv`, in front of the group's `monbus_arbiter`.
The scheduler and descriptor engine still emit unconditionally; the group
masks a packet whose type is `PktTypeCompletion` when the bit is 0 and forces
that emitter's ready high, so a disabled class never stalls either FSM. Only
Completion is gated: Error packets flow regardless of `ERR_EN`, which reaches
the group and gates nothing (the comment now says so; `PERF_EN` is not
implemented). No new ports anywhere, so the fub tests and the formal
harnesses are untouched; the group's FORMAL connectivity property keys on the
gated valids.

Proof of both states: `test_scheduler_group_beats_compl_enable_gate` runs one
descriptor flow with the bit at 0 (flow completes, zero Completion packets on
the group's bus) and again at 1 (a Completion appears); the top-level AXIS
monitor test, which programs `SCHED_CONFIG` with `COMPL_EN=0`, now requires
zero CORE Completion records in the capture -- the trace that surfaced this
issue -- then sets the bit and requires them back after one more transfer.
Register description rewritten in `rapids_engine_regs.rdl` (regenerated);
MAS scheduler-group port table, config-block mapping and monbus spec, and the
HAS monbus page, say the same.
