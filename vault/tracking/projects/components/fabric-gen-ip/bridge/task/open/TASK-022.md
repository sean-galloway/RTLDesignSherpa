# TASK-022: the 4x4's remaining uniform-traffic loss past saturation (not the response queue)

**Date:** 2026-10-25
**Priority:** P3
**Status:** OPEN
**Owner:** unassigned
**Where:** `bin/bridge_pkg/generators/adapter_generator.py` (the master adapter's read return across its width paths) -- a candidate, not a measurement
**Found by:** bridge TASK-021's measurement on `bridge_4x4_rw_rq8`, 2026-10-25

## Why

`[bridge] r_queue_depth` (bridge TASK-021) takes `bridge_2x2_rw` to 1.00 of
capacity under uniform traffic at every load. On the mixed-width, partially
connected `bridge_4x4_rw` it changes nothing: 2.44 / 2.46 / 2.45 slave
beats per cycle at gaps 8 / 4 / 2 against 2.37 / 2.44 / 2.43 unqueued
(FUNC, 48 reads per master, 2026-10-25) -- a flat ceiling near 2.45 from
1.4x offered on, whatever the load. The 24-read GATE sweep had shown 0.95
/ 0.74 of capacity, a transient the queues absorb; and `r_queue_depth =
32` measured the identical GATE curve to 8. So the 4x4's loss is not at a
shared slave's output at all. Permutation holds 0.90-1.00 and hot-spot
1.00 of capacity on the same fabric.

## What is known

- The 4x4 has one slave per width path per master, so each master's R
  comes back through four width converters, and the adapter returns R in
  AR issue order across those paths (its response mux follows the AR
  tracking FIFO). A read an idle path has answered waits behind an earlier
  read still at a busy path. This is the mechanism TASK-021 wrongly blamed
  on the 2x2 (where the adapter has one path); on the 4x4 it is a real
  candidate, unmeasured.
- A 256-bit master's 4-beat read is 32 beats at the 32-bit `periph`
  slave, so `capacity` sums per slave and the single slow port can bound
  the fabric regardless of the fabric itself; the per-slave offered figures
  in the log say whether that is the case at each gap.

## What to do

1. Probe per cycle, as TASK-021 did: each slave's R valid-and-not-ready
   against each master path's R port and the adapter's selected path.
   Measure before building anything.
2. If the adapter's in-order return is it: let R return out of AR order
   across paths when the IDs differ (AXI allows it; same-ID order is kept
   by the per-ID target gate already there). The remap slot or the
   `id_track_bits` table carries the target path.
3. Explain the flat ceiling: 2.45 slave beats per cycle regardless of
   offered load says a fixed resource binds -- an outstanding limit at the
   slow 32-bit `periph` port (a 256-bit master's read is 32 beats there),
   or the per-ID same-target gate. The per-slave offered figures in the
   log and each master's `ar_trk_full` say which.
4. Re-measure; if the 4x4 reaches the 0.85 floor, move `bridge_4x4_rw_rq8`
   into the pattern test's `QUEUED` set.

## Done when

- the 4x4's remaining loss has a measured mechanism, and either a fix or a
  documented reason it stays.
