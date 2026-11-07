# TASK-041: channel idle signal composition

> Migrated 2026-11-07 from `projects/components/dma-ip/rapids/TASKS.md` as **TASK-012**.

**Priority:** P1
**Status:** CLOSED -- delivered in an equivalent form, not the literal AND-of-all-engines the original proposed.
**Owner:** sean galloway

The original asked for `channel_idle` = scheduler idle AND descriptor engine
idle AND control engines idle AND program engine idle. Beats does it this way:

- `rtl/macro_beats/scheduler_group_beats.sv`: `assign sched_channel_idle = scheduler_idle;`
  -- the same as STREAM's `rtl/macro/scheduler_group.sv`.
- Descriptor-engine idleness is folded in locally
  (`w_desc_addr_fifo_empty && channel_idle && !r_apb_ip` in
  `descriptor_engine_beats.sv`).
- Control-engine idleness is implied: the scheduler cannot leave `CH_XFER_DATA`
  until `ctrlrd_idle` / `ctrlwr_idle` (`scheduler_beats.sv`).
- There is no program engine in beats.

**Not verified at migration:** whether the rapids TASK-014 drain-on-reset
window can hold a control engine busy while `scheduler_idle` is high. If
that matters, file it as an issue rather than reopening this.
