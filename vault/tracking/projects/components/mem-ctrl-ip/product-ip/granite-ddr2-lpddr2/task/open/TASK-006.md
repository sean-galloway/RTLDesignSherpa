# TASK-006 — close_page half-width traffic: an address-matching combiner at the store

**State:** open · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
**Source:** owner, 2026-10-29, after the TASK-005 verdict and the pumice
comparison: "Granite close half width traffic."
**Depends on:** TASK-005 (the port aggregator, measured and deferred),
pumice TASK-060 (pumice's write and read combiners, the reference form).

## Why

The 75 MHz board table (TASK-005, `char_*_half_threads_2026-10-29.csv`
against `char_pumice_rdmerge50_half_threads_2026-10-27.csv`), half-width
single beats, MB/s write / read:

| cell | pumice (CAM combiners) | granite, no aggregation | granite HALF_AGG, fixed ID |
|---|---|---|---|
| close_page pair walk, 1 thread | 98 / 98 | 30 / 37 | 60 / 75 |
| close_page pair walk, 2 threads | 192 / 193 | 49 / 59 | 49 / 59 |
| close_page pair walk, 4 threads | 179 / 185 | 96 / 96 | 96 / 96 |
| close_page oct walk, 1 thread | 85 / 49 | 30 / 37 | 30 / 37 |
| open_page pair walk, 1 / 2 threads | 195 / 147, 194 / 195 | 288 / 240, 287 / 288 | (hold costs 30 percent) |

Pumice's combiners merge on the DRAM address inside the CAM (matching
uncommitted `{bank, row, col}`), across threads and IDs, so they take 50
percent of the pair walk at every thread count and 43 percent of the oct
walk's writes at one thread. Granite's port aggregator (TASK-005) pairs
only same-ID adjacent halves and pays a hold on everything else; it wins
one cell. Under open_page granite needs nothing (it already beats pumice
there). The gap is close_page half-width traffic, and the form that closes
it is pumice's: match on the DRAM address at the store, not on the port.

## What to build

A combiner in `mc_bank_fifo_store` (common-ip, granite's store): on push,
a half-width column that matches an uncommitted queued entry's `{bank, row,
col}` in the same direction merges into it (write: the second half's data
and strobes into the staged write data; read: a second return ticket on the
same column) instead of taking a slot. The bank queues are age FIFOs
(TASK-002), so the match is against the queue's live entries, bounded by
the per-bank depth, and the merged entry keeps the older age. Telemetry:
merge counters per direction so `half_burst_family.aggregation()` reports
the ratio the way it does for pumice (`no merge / column-op telemetry on
this build` today).

Measure on the board with `half_threads` (both page modes, counter and
fixed IDs) and the four standard profiles for the no-regression check;
the target is the pumice column above, and the open_page column must not
move. Keep it behind a parameter with the OFF state tested
([[feedback-parameter-off-state-needs-its-own-test]]).

## Not this task

The port aggregator (TASK-005, deferred) and anything on the pick core
(TASK-003 item 5).
