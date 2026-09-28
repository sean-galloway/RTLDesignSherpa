# ISSUE-005: scheduler and descriptor-engine completion packets ignore SCHED_CONFIG.COMPL_EN

**Priority:** Low -- observability only; nothing functional depends on it.
**Status:** OPEN 2026-09-28. Surfaced by the rapids TASK-015 top-level monitor
test once rapids BUG-008 let packets through the monbus group: with
`SCHED_CONFIG` programmed `SCHED_EN=1, ERR_EN=1` (COMPL_EN = 0) the capture
trace still carried a Completion from the descriptor engine (agent 0x11/0x12)
and two from the scheduler (agent 0x31/0x32) for every transfer.

## What is known

`scheduler_group_beats.sv` line ~340 documents `cfg_sched_compl_enable` as
"(always enabled)": the input exists on the group and the array but does not
gate the emitter. The descriptor engine's fetch-complete packet has no enable at
all. Until BUG-008 the group's default `PKT_MASK` of 0xFFFF dropped everything,
so the bit looked honoured.

## Why an issue, not a bug

The intended behaviour is not written down: either the register bit should gate
these emitters (then it is a bug against the HAS `SCHED_CONFIG` description), or
completion packets are meant to be always-on and filtered only at the group
(then the register description and the config-block mapping should say so and
the bit retired). Decide, then file the bug or the doc fix.
