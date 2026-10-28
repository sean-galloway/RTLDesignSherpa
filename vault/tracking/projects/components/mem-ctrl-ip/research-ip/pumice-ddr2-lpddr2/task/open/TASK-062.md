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
**Status:** open (filed 2026-10-25)
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

(not started)
