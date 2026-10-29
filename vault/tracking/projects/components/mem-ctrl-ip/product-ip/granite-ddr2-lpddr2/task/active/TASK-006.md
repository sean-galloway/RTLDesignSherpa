# TASK-006 — close_page half-width traffic: an address-matching combiner at the store

**State:** active · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
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

## 2026-10-29, built and measured; one defect open

**What landed** (eca736f5f follow-on commit): `mc_bank_fifo_store MERGE_EN`
/ `granite_core STORE_MERGE_EN` (default 0). Write merge at admission: a
held AW matching a live, uncommitted, un-merged single-burst write entry
by {bank,row,col} takes no slot; its beats land in that entry under their
strobes (the data RAM gained byte enables, the strobes moved to flops and
OR), the entry leaves the schedulable set until the merge fill lands, a
commit decided before the merge waits for the fill at the drain fetch, and
the slot owes a second B with the merged id, blocked when any other live
write carries that id. Read merge at AR push: a key match against a live
unissued read entry (or the held AR) is a shadow of that ticket in the
return ring; the store takes nothing. `STORE_STATS_MERGE` /
`STORE_STATS_RD_MERGE` in granite's CSR (pumice's addresses), the host's
page-stats reader tolerant of granite's missing research counters, the
granite proxy with the half-burst families, `GRANITE_STORE_MERGE_EN` on
every build knob. Tests: `test_granite_core_merge[0,1]` (pumice ISSUE-026
filed from its OFF state at the default return-FIFO depth); proxy half
families, pair walk: every write and read pair merges at one thread, 34 /
48 percent at four, data clean; oct walk: none.

**Board, granite 75 MHz, STORE_MERGE_EN=1** (WNS +0.258, 37,195 LUT, +1.2k):
the four standard profiles are identical to the baseline on every cell
(`char_granite_merge75_{open_min,concurrent,multigen,paging_grade}`), and
`half_threads`, wr / rd MB/s:

| cell | pumice (its combiners) | granite base | granite MERGE, counter ids | granite MERGE, fixed id |
|---|---|---|---|---|
| close_page pair 1 / 2 / 3 / 4 thr | 98/98, 193/193, 193/193, 179/185 | 30/37, 49/59, 73/87, 96/96 | 60/75, 101/126, 144/175, 190/193 | 30/75, 49/123, 73/175, 86/193 |
| close_page oct 1 thr | 86/49 | 30/37 | 58/73 | 30/73 |
| open_page pair 1 / 2 thr | 195/147, 194/195 | 288/240, 287/288 | 293/243, 291/293 (**26,450 / 146 beats mismatched**) | 289/242, 287/293 |
| open_page pair 3 / 4 thr | 194/194, 157/194 | 255/280, 214/249 | 288/292, 275/289 | 263/292, 229/290 |
| open_page oct 1..4 thr | 191/147 .. 189/189 | 289/240 .. 214/248 | 287/245 .. 214/249 | 288/245 .. 214/248 |

Under close_page the pair walk doubles both ways at every thread count
and is now level with pumice; the open_page pair cells at three and four
threads gain 10 to 30 percent; nothing else moves. With one id per
thread only reads merge (the write rule blocks a same-id merge while an
older same-id write is live, and the pair's halves share the id), which
doubles reads alone and is clean on all 32 cells.

**Open defect:** with counter ids (both merges live) the open_page pair
walk at one and two threads returns corrupted data (26,450 of 64,000
beats at one thread, 146 at two; zero at three and four and under
close_page everywhere). The fixed-id run says the read merge is clean on
its own; the write merge under an open row at low thread count is the
suspect: the first half's column fires the moment its fill is done, so
the merge admission, the pick's registered request and the commit are
within a cycle or two of each other. Candidates in the store: a record
that re-enters the schedulable set when its own fill completes after the
merge was admitted (`fdone` set with `mgfill` still 1), or the merge fill
landing against a slot already in the drain. The DFI plane's write fire
waits for staged data, so a stalled drain cannot misalign the DRAM write;
the pick does revalidate `vld` at fire. Reproduction is in progress in
the granite proxy with the open policy and a long pair walk. Until it is
fixed `STORE_MERGE_EN` stays 0 (the product default) and the fixed-id
read-only form is the safe setting.
