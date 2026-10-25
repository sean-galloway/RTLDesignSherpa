# TASK-022: the 4x4's remaining uniform-traffic loss past saturation -- measured: the driver's ID rotation on the per-ID gate, then the traffic's own skew

**Date:** 2026-10-25
**Priority:** P3
**Status:** CLOSED 2026-10-25
**Owner:** bridge
**Where:** `dv/tbclasses/bridge_perf_patterns.py` (`open_loop`, the ID policy); the residual is architectural (`bin/bridge_pkg/rtl/bridge_id_remap.sv`'s `req_ok`, the masters' shared outstanding tables)
**Found by:** bridge TASK-021's measurement on `bridge_4x4_rw_rq8`, 2026-10-25

## Why

`[bridge] r_queue_depth` (bridge TASK-021) took `bridge_2x2_rw` to 1.00 of
capacity under uniform traffic at every load. On the mixed-width,
partially connected `bridge_4x4_rw` it changed nothing: 2.44 / 2.46 / 2.45
slave beats per cycle at gaps 8 / 4 / 2 against 2.37 / 2.44 / 2.43
unqueued (FUNC, 48 reads per master) -- a flat ceiling near 2.45 from 1.4x
offered on, whatever the load, and 32 queue beats measured the same as 8.

## What it was (measured per cycle, a probe test since removed)

Saturating uniform point (gap 2, FUNC) on `bridge_4x4_rw_rq8`, sampling
every slave R pin and every master adapter's AR gate, outstanding tracker
and per-path R valid once per fabric cycle:

- **The return path is clean.** Every slave R pin ran 0 percent stalled
  (the TASK-021 queues included); no path in any adapter held
  valid-not-granted data more than 7 percent of cycles. The task's
  candidate "the adapter returns R in AR issue order across its width
  paths" was refuted before the probe ran: the generated response mux is a
  per-beat round-robin over the width paths (the GitHub #119 L1 arbiter),
  not AR-order. `periph` ran at 0.98 beats/cycle -- saturated -- while
  `sram` and `gpu_mem` sat 84 percent idle: the loss was request SUPPLY.
- **The supply was the per-ID same-target gate, sprung by the driver.**
  31-58 percent of AR cycles were gated on `!ar_id_ok`
  (`bridge_id_remap`'s `req_ok`: an ID live toward one slave may only add
  requests to that slave -- AXI orders same-ID responses and two slaves
  cannot order between themselves) while `ar_trk_full` sat at 0 percent.
  The driver rotated `id = k % 16` against a target cycle of length 3, and
  16 mod 3 = 1 puts every burst's ID twin (16 bursts back) at a DIFFERENT
  slave, so under saturation nearly every AR waited on its twin's
  retirement -- each ID lane serialized behind the master's slowest read.
  The 2x2 never showed it: 16 mod 2 = 0 keeps the twin on the same slave,
  which is also why the 2x2's TASK-021 curve was the slave output's
  head-of-line blocking and not this.
- **The residual is the traffic, not the fabric.** With IDs partitioned
  per target the gate went to 0 percent and the 4x4's curve moved to 0.98
  of capacity at 1.4x offered (GATE length: 0.89 unqueued / 0.97 queued at
  3.5x) -- but the flat ceiling past 2x offered stayed (~2.55), now with
  dma0's tracker full 28 percent of cycles and gpu's ARs path-blocked 48
  percent. Half the uniform beats target the 32-bit `periph` port (offered
  7x its one beat per cycle at gap 2; a 256-bit master's 4-beat read is 32
  beats there): by Little's law each master's shared 16-entry outstanding
  table fills with periph reads, and a master's single AR channel issues
  in order, so its reads to the idle slaves wait behind periph-bound slots
  and periph's congested AR path. No fabric depth moves that wall; a
  deeper table only delays it.

## What was done

- `open_loop` partitions IDs per target (`t_idx * (16 // T) + round %
  (16 // T)`) -- a master that wants reads in flight to different slaves
  uses different IDs; that is what IDs are for. The 2x2 controls measure
  bit-identical curves before and after (the old rotation was already
  target-safe there), so TASK-021's mechanism and fix stand unmasked.
- The 4x4 fixtures stay on `KNOWN_UNIFORM_FLOOR` past 2x offered: the
  measured cost of a maximally skewed mix on minimal tables, documented in
  HAS 5.1 -- not a defect waiting on a fix. `bridge_4x4_rw_rq8` does not
  enter `QUEUED`: at FUNC length it is 0.65 of capacity at the worst
  point, not 0.85.
- HAS 5.1 carries the new 4x4 tables and both mechanisms; the handbook
  note `per-bank-queues-admit-from-the-pool`'s bridge paragraph carries
  the driver-side lesson.

## Done when

- [x] the 4x4's remaining loss has a measured mechanism (per-cycle probes:
      return path 0 percent stalled; ID gate 31-58 percent; then
      tracker-full / AR-path congestion at the oversubscribed 32-bit port)
- [x] and either a fix or a documented reason it stays -- both: the driver
      ID policy fixed (that part was the measurement, not the fabric), the
      architectural residue documented in HAS 5.1
