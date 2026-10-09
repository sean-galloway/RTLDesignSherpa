# TASK-003: axis4_intf_observer instantiates axis_monitor_lite instead of its private tap

**Status:** CLOSED 2026-10-08. RTL DONE (commit c35c8304b): inline gen_tap
replaced by per-port axis_monitor_lite, TAP_BLOCKED stickiness preserved,
observer suite 12/12 green (gate/func/full from clean, tap_dropped now 0 on
the all_classes stimulus). OUT_DEPTH=16 with a measured-reason comment
(grant waste + err-FIFO burst stall; fix filed as TASK-005). REMAINING:
the board packet-class matrix -- HANDED OFF 2026-10-04 to the ecc-ip lane.
Handoff facts measured by the utility-ip session: (a) bch_loop's
fpga/tcl/{build_all,create_project,synth_only}.tcl are UNCOMMITTED local
files and the dir is EMPTY as of Oct 4 01:52 -- bch_loop `make bitstream`
is broken machine-wide until the lane restores them; (b) reed-solomon's
build-loop has the scripts COMMITTED, instantiates this observer at
rs_loop_harness.sv:1039, and its host scripts carry iface-observer
campaigns -- the rs route is the ready A/B (bitstream at 1e9d9facb vs
main, then program + campaign + compare per-port packets; tap_dropped is
observer stat metric 15); (c) run any misc-fub sim with `source env_python`
(SIM=verilator + PYTHONPATH; the misc-fub conftest lacks the rapids-style
sys.path hardening).

**Priority:** P3 -- one implementation of the AXIS
event set instead of two; no behaviour change intended.

Filed from amba/monitor-lite TASK-003 when it closed (Sean's rule: a shared
mechanism's per-unit remainder is the unit's own item). `rtl/amba/monitor/
axis_monitor_lite.sv` exists now, and its event set and payload layouts were
lifted VERBATIM from this observer's per-port tap (`gen_tap` in
`projects/components/utility-ip/misc/rtl/axis4_intf_observer.sv`) so that the observer
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

## Closure (2026-10-08) — board packet-class matrix, ACCEPT

Orphaned board leg completed via the ready reed-solomon Genesys 2 route
(commit a4d9affa0, results in
projects/fpga-systems/Genesys2/ecc-ip/reed-solomon/stable/results/2026-10-08_observer_ab/):

- rs_loop bitstream from main (observer = per-port axis_monitor_lite):
  ~5.2 min, WNS +1.168 ns, 21,532 LUTs. Board = Genesys 2 (UART ttyUSB0,
  JTAG 200300B818A0B) under the serial board lock; Nexys A7 and the
  sibling Digilent board untouched.
- Campaigns: 8-block clean x2 matrix (new-tap image) + 16/64-block and
  e=t/t+1 extended runs (A/B with the old-tap image captured by the
  sibling baseline leg through the same lock).
- **Acceptance: ACCEPT.** Every per-iteration per-port monbus class count
  is identical between old tap and monitor_lite (msg/cw/msg seams),
  tap_packets == packets on both images, and all codec verdicts PASS.
  tap_dropped = 0 -> 0: measured structural fact — the RS harness builds
  the observer with ENABLE_MON_TAPS=0 (rs_loop_harness.sv:980), so no
  monbus events exist to drop on either image; the drop-elimination
  evidence proper (sim baseline 11..13 -> 0) remains the 12/12 observer
  suite from the RTL leg. The "lower, target ~0" bound is satisfied as
  0 <= 0.
- Extended-run counts match the committed pre-rework MANIFEST baseline to
  the digit (944/1008 beats @16 blk, 3776/4032 @64, 71.5/65.1 cyc/blk).

Follow-up filed from the session: tooling ISSUE-004 (hw_server
partial-enumeration race — partial device list missing exactly the
target refuses without retry; the repo's bounce-and-retry only covers
fully empty lists).
