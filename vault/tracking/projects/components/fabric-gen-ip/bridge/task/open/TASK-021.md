# TASK-021: head-of-line blocking under uniform traffic past saturation (in-order read responses across slaves)

**Date:** 2026-10-24
**Priority:** P3
**Status:** OPEN
**Owner:** unassigned
**Where:** `bin/bridge_pkg/generators/adapter_generator.py` (the master adapter's read response mux follows its AR tracking FIFO's head, so R returns in AR issue order across slaves)
**Found by:** bridge TASK-014's traffic patterns, `dv/tests/test_bridge_perf_patterns.py`, 2026-10-24

## Why

Under UNIFORM traffic past saturation -- every master alternating its reads
between both slaves, one 4-beat read every 2 cycles each, 4.0 slave beats
per cycle offered against a capacity of 2.0 -- `bridge_2x2_rw` accepts 1.35
beats per cycle (FUNC, `test_bridge_perf_patterns`; 1.61 at 1.33x offered).
`bridge_2x2_rw_pipe` is the same, `bridge_4x4_rw` 0.61 of its four ports.
The same fabric carries a PERMUTATION (each master its own slave) at 2.000
and a HOT SPOT (both masters one slave) at 1.000, i.e. at capacity.

The mechanism (2026-10-24, corrected by measurement): the master adapter
returns R in AR issue order across slaves -- its read response mux takes
the slave from the head of the AR tracking FIFO -- so a read the idle slave
has already answered waits behind an earlier read still queued at the busy
slave, and the idle slave's R channel sits on a beat nobody takes. The
request side was the first suspect (one in-order request stream into 2-deep
per-(master, slave) slots); it is not: 4- and 8-deep slots
(`xbar_slot_depth`, built and measured, then removed) gave the identical
curve at every load point. Dally & Towles ch. 3: uniform traffic hides
allocation conflicts, and this one only shows past saturation.

## What to do

1. Confirm in a wave: the master's R mux selecting the busy slave while the
   idle slave presents RVALID.
2. Fix direction: select the R source by the returned ID rather than by AR
   order. A remapped master (bridge_id_remap) already owns a slot per live
   ID; the slot can carry the target slave, and the response mux reads it
   from the returned slot index. A master that keeps its ID needs the same
   per-ID target the `id_track_bits` table already holds. Same-ID order is
   kept by the existing same-ID-different-slave gate; different IDs may then
   complete in any order, which AXI allows. B has the same FIFO and the
   same fix.
3. Re-measure the uniform curve; delete the KNOWN row in
   `test_bridge_perf_patterns.py` and re-table HAS 5.1.

## Done when

- uniform traffic at 2x offered load accepts >= 0.85 of capacity on
  `bridge_2x2_rw` and `bridge_2x2_rw_pipe`, the KNOWN row is gone, and the
  HAS 5.1 pattern table is re-measured.
