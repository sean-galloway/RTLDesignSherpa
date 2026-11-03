# TASK-062: ocelus on the memory controllers -- monbus event and error reporting from granite and pumice

> Source: owner, 2026-10-25, with the TASK-061 age-bit detail: "an error
> should be sent out on monbus. New task: ask ocelus to the memory
> controllers." Related: `rtl/amba/ocelus/` (axi_monitor_lite, the
> arbiter_*_monbus reporters, the error / timeout / threshold reporters),
> the shared decoder `bin/TBClasses/monbus` and `MonbusGroupHarness`
> ([[feedback-share-monbus-decoder]], [[feedback-monbus-group-harness]]),
> TASK-061 (the first controller-side error: a populated bank set with no
> oldest flag).

**Priority:** P2
**Status:** closed 2026-11-02 -- delivered under granite TASK-008 (one plane in common-ip, on both controllers)
**Owner:** TBD

## What is asked

Neither `pumice_top` nor `granite_core` references ocelus or monbus today;
their telemetry is CSR counters read over the UART. Put the ocelus monitor
on the controllers: a monbus port out of the top, the AXI slave port watched
by `axi_monitor_lite` (timeouts, response errors, the completion and
performance classes as configured), and a controller-side event source for
things the AXI monitor cannot see -- the first of them the TASK-061 age
invariant (ERROR class), then refresh overrun, a write-merge fallback,
a ragged burst. The harness already carries a monbus consumer stack from
STREAM (the monitor board-validation env, the group harness), so the
board side is a wiring job; the sim side uses the shared decoder, never an
inline shift / mask.

## To settle

- Which monitor form: `axi_monitor_lite` (677 LUT on STREAM) is the fit for
  granite; pumice can take the full monitor.
- The controller event packet: one producer per controller with a small
  event code space, routed through the same monbus arbiter the AXI monitor
  uses (`arbiter_*_monbus`), so one port leaves the top.
- The CSR counters stay; monbus is the event path, not a replacement for
  the deltas the host reads.

## What landed / Measured / Gates

Delivered as granite TASK-008 (37d6e00e6, 2026-11-01; board timing in
c38f80c9e, 2026-11-02): it was filed there because the plane is common-ip
and granite was the first board target. What this task asked for, item by
item:

- **A monbus port out of the top**: `mc_ocelus_plane` (common-ip) behind
  `HAS_MON` (default 0) on `granite_core`, `pumice_core` and every top,
  leaving as ONE AXI-Lite master (`m_axil_mon_*`) through
  `monbus_axil4_group_1wr`: an error window with `mon_irq_o` and a trace
  window. Config in the `MON_*` CSRs (pumice at 0x200).
- **The AXI slave port watched**: two passive `axi_monitor_lite` taps (read,
  write) -- the lite form for both controllers, not the full monitor for
  pumice: one plane, one area figure, and the lite form carries the
  timeout / error / completion classes asked for.
- **A controller-side event source**: `mc_monlite`, `PROTOCOL_CORE`, codes
  in `mc_common_pkg::mc_event_e`. Errors: cal_err, zq_overdue, refresh
  backlog at maximum (the "refresh overrun"), ragged AW (the "ragged
  burst"), read beat lost, return-ring orphan, dropped. Debug: init done /
  state, direction flip, REF / ZQ issued, page-timeout PRE, store full,
  ring full. Drop-and-count, never stalls.
- **Through the ocelus arbiter**: a 3-client `monbus_arbiter`.
- **Sim side on the shared decoder**: `McOcelusTB`
  (`pumice-ddr2-lpddr2/dv/tbclasses/mc_ocelus_tb.py`) runs the same checks
  for both: `test_pumice_ocelus.py` (6 cells, on and off) and
  `test_granite_ocelus.py`. `test_mc_monlite.py` covers the event FUB.
- **The CSR counters stay**: they do; monbus is the event path.

**Board.** Granite, 2026-11-02: 100 MHz, WNS +0.006, `seq_ocelus` clean
(completions 64 / 64 and 1000 / 1000, real errors 0) -- see granite
TASK-008. Pumice's plane is the same RTL and is sim-verified; no pumice
board build with `HAS_MON = 1` has been made (pumice's combiner text does
not hold 75 MHz even without it, TASK-060).

**Two named events have no source, so they were not built.**

- *The TASK-061 age invariant* (a populated bank set with no oldest flag):
  no RTL computes it, and granite compiles the ages out by default
  (`HAS_AGE = 0`, pumice TASK-059). Error code 0x07 is free for it if
  `HAS_AGE` is ever turned on.
- *A write-merge fallback*: neither combiner has a fallback path to report.
  Pumice's write combiner either merges or allocates, and both outcomes are
  already counted.

Re-gated 2026-11-02: pumice `run-all-func-both` 222 / 222, granite top
22 passed / 1 xfail.

