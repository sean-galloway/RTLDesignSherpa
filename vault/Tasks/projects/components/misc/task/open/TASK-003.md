# TASK-003: axis4_intf_observer instantiates axis_monitor_lite instead of its private tap

**Status:** open 2026-09-27  **Priority:** P3 -- one implementation of the AXIS
event set instead of two; no behaviour change intended.

Filed from amba/monitor-lite TASK-003 when it closed (Sean's rule: a shared
mechanism's per-unit remainder is the unit's own item). `rtl/amba/monitor/
axis_monitor_lite.sv` exists now, and its event set and payload layouts were
lifted VERBATIM from this observer's per-port tap (`gen_tap` in
`projects/components/misc/rtl/axis4_intf_observer.sv`) so that the observer
could adopt the core. Two things the core does differently, on purpose:

- **Two events per cycle** into a 4-deep unreset queue, instead of one into a
  hold register. On a stream, events coincide (the beat ending a bubble is a
  RESUME and, with TLAST, a STREAM_END; a TID change may be the first beat
  after a pause); the one-per-cycle pick dropped and counted the loser every
  time, so the observer's `tap_dropped` reports ordinary traffic. Expect that
  count to fall to zero on the same stimulus.
- **The drop report waits for an empty queue** (the count still saturates and
  is reported; it just never takes the slot a live event needs).

The work: replace each `gen_tap` body with an `axis_monitor_lite` instance
(UNIT_ID / AGENT_ID as today: `{8'h00, 4'h2, 4'(gi)}`; `cfg_stall_threshold`
takes MON_LATENCY's role; the per-class enables map one to one; `cam_clear`
to `clear`), keep `tap_packets` from `packet_count` and `tap_dropped` /
`tap_lost` from `dropped_count`, rerun the observer test suite and the board
packet-class matrix (memory: all 7 classes were emittable on the lite-tapped
observer build). The AXI tap (`axi_monitor_lite` per port) stays as is.

Acceptance: observer tests green at FULL from clean; per-iteration monbus
class counts unchanged on the board build except `tap_dropped`, which should
be lower; the observer no longer contains a second copy of the AXIS event
table.
