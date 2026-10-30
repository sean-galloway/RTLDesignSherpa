---
title: TASK-004 — granite 100 MHz timing margin: the remaining levers, parked
summary: The levers left after the 100 MHz close (LA=3 pick split, scheduler-plane pblock, registered read-issue strobe, directive overrides, flop replication), each with its measurement, parked until an edit breaks the close or the product point moves above 100 MHz.
---

# TASK-004 — granite 100 MHz timing margin: the remaining levers, parked

**State:** deferred · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
**Status:** deferred 2026-10-29 -- pending a build that no longer closes at
100 MHz with the shipped directives, or a product point above 100 MHz.
**Parent:** TASK-003 (the close itself: b8665155e, results log 2026-10-28
evening and 2026-10-29).

## Why parked

Owner, 2026-10-29: "if timing converges, even if barely, why should we spend
more effort at this point?" The committed text closes at WNS +0.004 ns, 0 of
107,847 endpoints, deterministically (an identical rebuild reproduces it line
for line). Static timing already carries the device corners, so the bitstream
is legal and the thin margin costs nothing today. What the margin does say is
the price of the next edit: a different placer (ExtraTimingOpt) lands four
pick-select endpoints at -0.072 ns, so any change that reshuffles placement
has about even odds of reopening the close. These levers are the response to
that event, not work to do now.

## The levers, with what each measured (100 MHz, AltSpreadLogic_high)

| lever | measured | verdict |
|---|---|---|
| LA=3 split of the pick pipeline (fire checks one stage earlier, the select on registered candidates) | not built; the owner's call per TASK-003 | the only lever that removes levels from the pick select (11-14 today); costs a cycle of pick latency, perf proxy must be re-run |
| scheduler-plane pblock (pick + 16 bank timers + global timers in one region) | not built | the worst path is 71% route (9.975 ns data path, 7.120 route); precedent `stream_char` monbus-CAM floorplan |
| register the read issue strobe into the ring | not built | a 36-load LUT net mid-cone in the 2026-10-28 census; smaller than the timer loads were |
| placer directives: ExtraTimingOpt / ExtraPostPlacementOpt / Explore | -0.228 / -0.227 / -0.575 on the -0.114 baseline; ExtraTimingOpt -0.072 on the closed text | inside the between-netlist spread; not a lever, keep the shipped AltSpreadLogic_high + Explore route |
| `r_hold` MAX_FANOUT 32 (flop replication) | -0.297, 34 failing, the replica still on the path | replication moves the cusp, twice now (also `r_spec_taken_replica` under the trimmed pick) |
| pick tail trim (pre-decoded request flops) | -0.219 / 20 alone; -0.014 / 2 with SET_LAG where the untrimmed pick leaves none | reverted; no level gain |

## What un-defers it

Either of:

- a committed change leaves the granite 100 MHz build negative under the
  shipped directives (`make bitstream` with `GRANITE_SYS_100=1`, no
  PLACE_DIRECTIVE override): take the LA=3 split first, pblock second;
- the product point moves above 100 MHz.

Reading order when it wakes: TASK-003 results log entries "2026-10-28
evening" (fanout analysis, the SET_LAG design) and "2026-10-29" (the margin
probe), then `targets/granite/fpga/reports_sys100_2026-10-28_timer_set_lag/`.
