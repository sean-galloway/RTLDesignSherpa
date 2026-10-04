# TASK-005: the single-port observer's monbus arbiter padding wastes every other grant, and the egress err FIFO back-pressures the taps in bursts

**Status:** CLOSED 2026-10-04 as a measurement-driven disposition — the fix
that survives verification is narrower than the task as filed, and the
filed root cause was REFUTED.

What landed:
- Width guards `(CLIENTS>1) ? $clog2(CLIENTS) : 1` in
  arbiter_round_robin, arbiter_priority_encoder, and monbus_arbiter, so
  CLIENTS=1 elaborates (lint-verified); the observer's two-client padding
  (ARB_CLIENTS + gen_arb_pad) is deleted and it now builds the arbiter with
  exactly NUM_PORTS clients. Observer suite 12/12 green (gate/func/full).
- arbiter_round_robin formal proof: PASS with the guards.

What was disproven:
- The filed claim "the idle padding client wastes every other grant" is
  FALSE. The measured 1/1 monbus_ready toggle is the arbiter's DOCUMENTED
  single-requester ACK-mode dead cycle (header: "Single request + ACK
  completion = mandatory dead cycle"): the wrapper's ack
  (grant && valid && downstream-ready) completes a transfer the moment
  ready lands, after which the client may legally withdraw valid, so
  re-granting combinationally in the ack cycle holds a grant nobody wants.
  Measured 2026-10-04: removing the dead cycle (merging ack-mode Rules 3+4)
  FAILS the monbus_arbiter formal proof (ap_no_spurious, step 5 — output
  valid locks high on a withdrawn request). The change was reverted; the
  experiment and its evidence are recorded in the arbiter's header and
  version history. Padding removal is throughput-neutral by the same fact.
- Separately measured: formal/common/monbus_arbiter's ap_no_spurious is
  PRE-EXISTING RED — it fails at HEAD with and without these changes (the
  parallel lane is editing its flat). Not caused by, and not fixed under,
  this task.

Consequence: the observer's OUT_DEPTH stays 16 (the egress err-FIFO burst
stall is the binding constraint; the tap queue needs the depth to ride it
out). The RTL comment now says exactly that.
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
