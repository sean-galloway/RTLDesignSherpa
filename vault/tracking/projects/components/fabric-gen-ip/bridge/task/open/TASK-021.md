# TASK-021: head-of-line blocking under uniform traffic past saturation (2-deep request slots)

**Date:** 2026-10-24
**Priority:** P3
**Status:** OPEN
**Owner:** unassigned
**Where:** `bin/bridge_pkg/generators/crossbar_generator.py` (`_generate_request_slots`, `DEPTH(2)`), `adapter_generator.py` (the master adapter's single AR/AW stream)
**Found by:** bridge TASK-014's traffic patterns, `dv/tests/test_bridge_perf_patterns.py`, 2026-10-24

## Why

Under UNIFORM traffic past saturation -- every master alternating its reads
between both slaves, one 4-beat read every 2 cycles each, 4.0 slave beats
per cycle offered against a capacity of 2.0 -- `bridge_2x2_rw` accepts 1.36
beats per cycle (GATE, 24 reads per master; the FUNC curve is in HAS 5.1).
The same fabric carries a PERMUTATION (each master its own slave) at 2.000
and a HOT SPOT (both masters one slave) at 1.000, i.e. at capacity. So a
third of the fabric sits idle only when each master's request stream mixes
targets: a master adapter presents its ARs in order on one stream; the
crossbar steers each into a 2-deep request slot per (master, slave); when
the slot toward the busy slave is full the AR behind it, bound for the idle
slave, waits -- head-of-line blocking at the adapter -> slot boundary.
Dally & Towles ch. 3 is explicit that uniform traffic hides allocation
conflicts; this one shows only past saturation, where a real system spends
its bursts.

## What to do

1. Confirm the mechanism against the slot occupancy in a wave (both slots
   toward the busy slave full, the adapter's AR stalled with a different
   target).
2. Candidate fixes, in order of cost: a per-slave slot depth key
   (`xbar_slot_depth`, default 2 = the sizing rule's minimum for rate;
   deeper buys decoupling, not rate -- measure 4 and 8 on the uniform
   curve); virtual-output queuing at the master adapter (one issue queue
   per target slave, bridge TASK-016's rule then sizes each). Weigh the
   LUTs against the recovered 0.6 beats per cycle.
3. Until fixed, `test_bridge_perf_patterns.py` holds the uniform-overload
   points to a KNOWN floor at the measured level (0.60 of capacity) with
   this task's ID; delete that row when the fix lands and the 0.85 floor
   applies again.

## Done when

- uniform traffic at 2x offered load accepts >= 0.85 of capacity on
  `bridge_2x2_rw` and `bridge_2x2_rw_pipe`, the KNOWN row is gone, and the
  HAS 5.1 pattern table is re-measured.
