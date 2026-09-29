# TASK-004: timeout and latency events lose the one-per-cycle pick to a sustained error stream; hold the payload until queued

**Priority:** P3
**Status:** CLOSED 2026-09-28
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

- [x] the duty-1 arm of the lite starvation test delivers the victim's timeout
- [x] the soak's accounting identity still closes exactly
      (`test_axi_monitor_soak_monlite`)
- [x] formal/amba/axi_monitor_lite prove + cover still pass

**2026-09-28, later:** the LATENCY half is done under ISSUE-002 -- the latency
event is now decided a stage after its completion and held with its own
payload (id, address, latency). What remains here is the TIMEOUT half: hold
the scan-hit event (with `r_id`/`r_addr` of the timed-out slot and its code)
until the pick takes it, using the same shape.

---

## CLOSED 2026-09-28

Both halves done. The latency half landed under ISSUE-002 (compare a stage
later, payload held). The timeout half: one fired timeout the pick could not
take (an Error outranked it, or the queue was full) is held with its own
payload -- code, id, address captured while the timed-out slot still holds
them -- and offered on the following cycles, oldest first; a second fresh
timeout arriving while the hold is full is still lost and counted. Both
holds are now in `busy`.

The drop accounting was restructured with it, and that fixed a latent bug:
`w_lost = offered - take` subtracted the take of a HELD event from a total
that only counts FIRED events, so a held latency packet going out with the
bus free underflowed the 4-bit count by 15 and produced a bogus
`EVENT_DROPPED(15)` report. Nothing checked for it; the lite TB's latency
phase now asserts no drop report follows a latency packet.

| Check | Result |
|---|---|
| `test_axi_monitor_pktgen_timeout_starvation_monlite`, duty 1 per cycle | victim timeout DELIVERED, 400/400 errors, 0 drops (was LOST) |
| same, duty 1 in 2 | DELIVERED, 0 drops |
| `test_axi_monitor_soak_monlite` 60k cycles | 10,663 generated == 7,583 + 982 + 2,005 delivered + 93 reported + 0 pending |
| `val/amba/monitor-lite` from clean | GATE 108/108, FUNC 201/201 |
| `val/amba` from clean | GATE 839/839, FUNC 1055/1055 |
| `formal/amba/axi_monitor_lite` | prove + cover PASS |
| Artix-7 lite bridge fixture, 10 ns | WNS +0.366 ns, 0 failing; worst path is the lite's timeout scan, 8.8 ns, 10 levels |
