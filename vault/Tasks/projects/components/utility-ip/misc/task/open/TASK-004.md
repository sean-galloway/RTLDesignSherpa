# TASK-004: the single-port observer's monbus arbiter padding wastes every other grant, and the egress err FIFO back-pressures the taps in bursts

**Status:** open 2026-10-04
**Priority:** P3
**Filed from:** utility-ip/misc TASK-003 (observer adopted axis_monitor_lite).

TASK-003 replaced the observer's inline AXIS tap with the shared
`axis_monitor_lite` core. One integration finding is worth its own item:

`axis4_intf_observer` pads `monbus_arbiter` to `ARB_CLIENTS = max(NUM_PORTS,
2)` because a single-client build sizes the arbiter's grant id as `[-1:0]`
and Verilator refuses it (ASCRANGE) -- the comment is in the observer. The
padded client is tied idle, but `arbiter_round_robin` (ACK mode) still
rotates the grant through it: measured on the all_classes FULL build
(2026-10-04, FCD of a failing run), `monbus_ready` to the sole real client
toggles 1/1 -- every other grant cycle is spent on a client that can never
transfer. Single-port observers therefore drain their taps at HALF rate.

Downstream of that, the egress path (err FIFO, default 64 records, 3 AXIL
beats per record) back-pressures in bursts whenever stimulus out-runs the
AXIL drain. With the old inline tap this was invisible: the tap shed load by
priority-picking one event per cycle and silently counting the losers
(baseline all_classes FULL logged tap_dropped=11..13 and still passed --
the drops never became packets). The faithful core queues coincident events
instead, so the full event stream reaches the egress and the burst
back-pressure lands on the tap queue, where FIFO-order shedding can drop
high-value classes (measured: Channel/ID_CHANGE and DEST_CHANGE lost at
OUT_DEPTH 4 and 8).

TASK-003's integration sets the core's OUT_DEPTH to 16 with a comment, which
rides out the measured 8-cycle stall at ~1.1 events/cycle. That is a
workload-sized buffer, not a fix.

## Done when

- `monbus_arbiter` (or `arbiter_round_robin` behind it) no longer spends a
  grant cycle on a client with no request -- single-port observers drain at
  full rate. The `[-1:0]` grant-id width is guarded
  (`(CLIENTS>1) ? $clog2(CLIENTS) : 1`) so CLIENTS=1 elaborates everywhere,
  and the observer's padding (and its comment) is deleted.
- `val/amba/test_monbus_arbiter_grant_hold.py` and the val/common arbiter
  suite still pass; a single-client build of the observer sims green at FULL
  with the core's OUT_DEPTH back at its default 4.
- Re-measure: during the all_classes FULL burst, `monbus_ready` to a sole
  client no longer toggles 1/1.
