# TASK-004: timeout and latency events lose the one-per-cycle pick to a sustained error stream; hold the payload until queued

**Priority:** P3
**Status:** open
**Owner:** TBD (monitor-lite)
**Filed:** 2026-09-28 from amba/monitor-lite TASK-002 (the inherited starvation suite)
**Related:** amba TASK-083 (the full monitor's starvation measurement)

## What was measured

`val/amba/test_axi_monitor_pktgen.py::test_axi_monitor_pktgen_timeout_starvation_monlite`
drives one stalled read against a sustained SLVERR flood on the other IDs
through `axi_monitor_lite` (4 entries):

| error duty | errors delivered | victim timeout | drop reports |
|---|---|---|---|
| 1 per cycle | 400 / 400 | LOST, counted in dropped_count | 1 |
| 1 per 2 cycles | 200 / 200 | delivered | 0 |

The accounting is exact in both arms (every generated event is delivered or
counted), which is the lite's promise. But the loss mechanism is structural,
not backpressure: the lite picks ONE event per cycle, Error above Timeout,
and a timeout is a one-cycle pulse from the rotating scan (`r_e_scan_hit`).
If an error fires in that same cycle the timeout loses the pick and is gone;
the entry's `r_tmo` is latched so it never re-fires. At 50 % error duty that
is a coin flip per timeout.

## What to change

Hold a timeout event until it is queued, as the latency event already is
(`r_lat_pend`), and hold its PAYLOAD (id, address, code), not the slot index:
the timed-out entry can complete and be reallocated while the event waits,
and a slot-indexed hold would then name the new transaction's address. The
existing `r_lat_pend`/`r_lat_slot` hold has that same hazard (a completed
slot can be reallocated the next cycle) and should move to a payload hold at
the same time. Cost is about IW+AW+8 flops per held event; the drop counter
stays as the report of last resort for a queue that is genuinely full.

## Done when

- [ ] the duty-1 arm of the lite starvation test delivers the victim's timeout
- [ ] the soak's accounting identity still closes exactly
      (`test_axi_monitor_soak_monlite`)
- [ ] formal/amba/axi_monitor_lite prove + cover still pass
