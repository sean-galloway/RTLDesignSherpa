# TASK-021: head-of-line blocking under uniform traffic past saturation (a shared slave's in-order R output)

**Date:** 2026-10-24
**Priority:** P3
**Status:** CLOSED 2026-10-25
**Owner:** bridge
**Where:** `bin/bridge_pkg/generators/crossbar_generator.py` (`_generate_response_queues`, `_rq_on`, the response arbiters and muxes), `bin/bridge_pkg/config_loader.py` (`[bridge] r_queue_depth`)
**Found by:** bridge TASK-014's traffic patterns, `dv/tests/test_bridge_perf_patterns.py`, 2026-10-24

## Why

Under UNIFORM traffic past saturation -- every master alternating its reads
between both slaves, one 4-beat read every 2 cycles each, 4.0 slave beats
per cycle offered against a capacity of 2.0 -- `bridge_2x2_rw` accepted
1.35 beats per cycle (FUNC, `test_bridge_perf_patterns`; 1.61 at 1.33x
offered). `bridge_2x2_rw_pipe` the same, `bridge_4x4_rw` 0.61 of its four
ports. The same fabric carried a PERMUTATION at 2.000 and a HOT SPOT at
1.000, i.e. at capacity.

## What it was

Measured per cycle at the ports (a probe test, since removed): both slaves'
R channels sat valid-and-not-ready 31 percent of the cycles; no master R
port ever did; the masters' ARs waited on their outstanding limit; the
request slots were nearly empty. A slave returns R in its own order. When
its head burst is for the master whose R port the other slave's burst is
holding, it stalls, and the master its next burst was for sits idle:
head-of-line blocking at the slave's output. Only uniform traffic shows it
-- a permutation never shares a master port, a hot spot has no second
slave.

Two earlier suspects, each refuted by building it: 2-deep request slots
(4 and 8 measured the identical curve; `xbar_slot_depth` built and removed)
and the master adapter's in-order R mux (this task's text blamed it for a
day; the 2x2 adapter has one width path and selects nothing).

## What was done

`[bridge] r_queue_depth = N` (default 0): one `gaxi_fifo_sync` of N R beats
per (reading master, shared slave) pair inside the crossbar. The slave
writes a beat into the queue the returned bridge id names (its RREADY for
that master is the queue's write ready); the master's response arbiter
requests from the queue head, the R mux takes it, and the drain is grant
AND the master's RREADY. Not on a CDC lane (its own FIFO already decouples
it) nor on the internal subtractive slave; not on a slave with one reader.
A width path with one slave grants from the queue head, not the slave's
head beat -- the first cut followed the slave and stranded a master's queued
beats whenever the slave idled or served another master; every pair of the
4x4 hung (fixed, unit-tested).

Measured (FUNC, 2026-10-25, HAS 5.1):

| Fixture | uniform 1.33x offered | uniform 2x (4x on the 4x4) |
|---|---:|---:|
| `bridge_2x2_rw` (unqueued) | 0.80 of capacity | 0.67 |
| `bridge_2x2_rw_rq8` | 1.00 | 1.00 |
| `bridge_4x4_rw` (unqueued) | 0.79 | 0.61 |
| `bridge_4x4_rw_rq8` | 0.79 | 0.61 |

On the 2x2 the loss is gone and latency at 2x offered falls from 159 to 96
cycles (the permutation's figure); the price is one cycle of R latency at
every load (the FIFO's mux read) and the flops: the 2x2 crossbar goes from
1,883 to 3,235 flops on ASAP7 at an unchanged worst path, and on the
Kintex-7 from 4,605 to 5,058 FFs on the whole top with the storage in
distributed RAM (HAS 5.3). On the 4x4 the same key changes nothing at
FUNC length (2.45 against 2.43 slave beats per cycle at 4x offered; the
shorter GATE sweep showed 0.74 of capacity, a transient the queues absorb,
and 32 beats measured the same as 8), so the 4x4's loss is another stage
entirely -- filed as bridge TASK-022.

The default stays 0 by the rule that every depth defaults to its minimum
(bridge TASK-016); the unqueued fixtures keep their measured curve and the
pattern test holds them to 0.55 of capacity past saturation as the
documented cost of the minimum. `bridge_2x2_rw_rq8` is held to the full
0.85 floor.

## Done when

- [x] the mechanism measured, not inferred (per-cycle port stalls)
- [x] `r_queue_depth` in the generator, the loader, the sizing report and
  `<bridge>_sizing.json`; unit tests for the key, the emitted RTL and the
  single-slave grant
- [x] `bridge_2x2_rw_rq8` and `bridge_4x4_rw_rq8` fixtures, generated suite
  plus the pattern sweep; uniform traffic at 2x offered on `bridge_2x2_rw_rq8`
  at 1.00 of capacity
- [x] HAS 5.1 / 5.3 / 6.2 / 6.4, MAS 2.3 / 7.1, PRD, CLAUDE.md and the
  handbook note `per-bank-queues-admit-from-the-pool` corrected to the
  measured mechanism (the adapter-mux text is gone)
