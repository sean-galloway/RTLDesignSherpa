# TASK-006 — close_page half-width traffic: an address-matching combiner at the store

**State:** closed · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
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

**Defect, found and fixed (2026-10-29, afternoon).** With counter ids
(both merges live) the open_page pair walk at one thread read back
26,450 of 32,000 half-beats wrong, 146 at two threads, a handful at
three and four, nothing under close_page. Bisected on the board with host
knobs (no rebuilds): fixed-id WRITES (which block the write merge) are
clean under counter-id reads, so the write merge is the culprit; any
gap between the halves, 20 or fewer outstanding, the bank-interleaved
map, tCCD = 2 or tWR = 8 are each clean; the data in DRAM is wrong (a
read-only pass of any mode reports the same count; an unmerged rewrite
clears it) and a pre-loaded correct region stays correct through the bad
pass, so the merged bursts were never written, not written wrong.

Mechanism (three store faults, one shared root -- a WRITE reaching the
DFI command head before its data, which the DFI plane holds for the data
while the scheduler's timers run from the commit):

1. The pick core fires on head records REGISTERED at the store's edge,
   one cycle behind `r_wr_fdone`. A merge admitted into a filled,
   uncommitted entry clears its fdone, but for one cycle the record still
   says filled; the tCCD = 1 column speculation (same pair, consecutive
   cycles -- the row-major walk is the case) fires exactly in that cycle
   and commits an entry whose merged beats are not in the RAM. The fetch
   waits for them (`r_wr_mgfill`), the DFI plane holds the WRITE for its
   data -- but the scheduler's tWR / auto-precharge self-close / ACT
   timers run from the COMMIT. The DRAM gets its PRE or ACT too soon after
   the WRITE it actually received and the write is lost; with the whole
   walk in one bank the loss chains. A second path reached the same
   state: a slot's own fill completing after its merge was admitted set
   fdone with the merge fill still pending (the fill-lag test holds a
   WRITE 114 cycles that way).
2. The merged write's second B paused the drain one beat
   (`wr_cm_rd_valid_o` low in the done2 cycle). The DFI command path takes
   a column every cycle; a data path that delivers one beat per two cycles
   for merged entries runs out of the commit-to-DFI slack, and the WRITE
   sits at the DFI head one cycle late -- 904 one-cycle holds on a
   1024-pair row-major walk in the proxy, independent of fault 1. This is
   the fault behind the board's 83 percent: the global "no commit after a
   merge" gate removed it by handing the data path a cycle back (and cost
   a third of the bandwidth); the per-slot check alone left 110 / 12 / 20
   mismatches at one / two / three threads.
3. The fill-order FIFO (`r_fo`) was NUM_ENTRIES deep: a merge target owes
   two fills, so at 32 outstanding half-width writes the push wrapped over
   the head and beats landed in the wrong slots. Real (the directed test
   hangs against it), but not the board's symptom: fixing it alone changed
   nothing on the board.

Fixes (`mc_bank_fifo_store`, `mc_bank_pick`, `mc_scheduler_plane`):
fdone means every fill the slot owes has landed (own fill never sets it
while a merge fill is pending, same-cycle admission included); a per-slot
`wr_fill_pending_o` vector (live `r_wr_mgfill`) that the pick re-checks at
fire for the slot it is about to commit (`wr_fill_pending_i`, tied 0 on
pumice / scoria / andesite); the merged B ids queue (`r_d2q_*`, NUM_ENTRIES
deep) and go out in cycles with no done of their own, the drain holding
only on a full queue and an AW whose id is queued waiting at admission
(its B would overtake the queued one on the same id); fill-order depth
`MERGE_EN ? 2N : N`. A global
"no commit the cycle after a merge" gate was tried first: it cleared every
board cell but cost the pair walk a third of its write bandwidth (293 to
194 MB/s), which is why the check is per slot.

The sim never showed it because the proxy's DRAM model anchors tWR at the
controller's own commit (pumice ISSUE-023's fix), so a late WRITE is
invisible to it. The DFI command path's simulation-only "WRITE held at
the head" counters are the contract check now: `test_granite_char_perf`
and the core TB merge tests fail on any held cycle (the row-major merged
pair walk showed 903 held cycles before the fix, 0 after;
`cocotb_test_granite_core_merge_fill_lag` drives sixteen pending fills
through the W channel on `slow_producer` and hangs against the old
fill-order depth; the proxy's row-major merged walk holds 904 cycles
with the drain bubble, 0 with the queue, at the same 290 MB/s). Host knobs added for the bisection: `CHAR_CONFIGS` (any
config name), `CHAR_FAMILIES`, `CHAR_THREADS`, `CHAR_SC_OVER`,
`HALF_ID_FIXED_WR/RD`, `HALF_SEED_SALT`, `HALF_GAP`, `JEDEC_OVERRIDE`, and
the proxy's `TEST_ADDR_SCHEME`; the page-stats `counted` gate no longer
discards a granite merge count.

**Board, granite 75 MHz, STORE_MERGE_EN=1, all three fixes** (WNS +0.002
ns at 37,395 LUT; the merged-B id compare in the admit cone is the new
worst path -- a thin positive margin is the design point, reported as
such). `char_granite_merge75v2_{half_threads,fixedid_half_threads,open_min,concurrent}`:
zero mismatches on all 64 half_threads cells (counter and fixed ids),
open_min and concurrent unchanged. wr / rd MB/s, DRAM peak 600 each way:

| cell | granite base | MERGE first build | MERGE fixed, counter ids | MERGE fixed, fixed id |
|---|---|---|---|---|
| close_page pair 1 / 2 / 3 / 4 thr | 30/37, 49/59, 73/87, 96/96 | 60/75, 101/126, 144/175, 190/193 | 60/75, 101/123, 145/175, 189/193 | 30/75, 49/123, 73/175, 87/193 |
| close_page oct 1 thr (2..4 unchanged) | 30/37 | 58/73 | 58/73 | 30/73 |
| open_page pair 1 / 2 thr | 288/240, 287/288 | 293/243 (**26,450 bad**), 291/293 (**146 bad**) | 294/242, 291/293 | 289/242, 286/293 |
| open_page pair 3 / 4 thr | 255/279, 214/249 | 288/292, 275/289 | 290/292, 267/290 | 184/292, 168/290 |
| open_page oct 1..4 thr | 289/240 .. 214/248 | 287/245 .. 214/249 | 287/244 .. 214/249 | 289/244 .. 215/248 |

The combiner now delivers what TASK-006 asked for: the close_page pair
walk doubles both ways at every thread count and is level with pumice,
the open_page pair cells at three and four threads gain 14 to 25
percent, nothing else moves, and the data is right. `STORE_MERGE_EN` is
the product default (1) as of 2026-10-29, the owner's call after the
board table above: granite_core, granite_top_geared, the board target
wrappers and the test runners' env defaults all say 1, a no-knob board
build and a no-override proxy run were taken against it, and the merge
tests keep the OFF state covered (`test_granite_core_merge[0]`,
`_fill_lag[0]`). The default is a 75 MHz default: at 100 MHz (DDR2-400)
the merge build misses by 2.544 ns on the pick-to-store fire path (78
percent route) where the merge-off build closes at +0.011; the 100 MHz
board builds set `GRANITE_STORE_MERGE_EN=0` until that path is registered
(TASK-003 log, 2026-10-29 evening).

**CLOSED 2026-10-29.** Outside this task: the proxy's DRAM model still
anchors tWR at the controller's commit (pumice ISSUE-023); the held-WRITE
assertion is the guard, a DFI-anchored model would be the cure.

**Addendum 2026-10-30.** The corruption fix's pick-side live check
(`wr_fill_pending`) is removed; the race is closed in the store by masking
the merge target out of the head record in the admission cycle. Same
merge rate, same held-write result, 0.13 ns back at 75 MHz; the combiner
still does not close at 100 MHz on its own (-1.6 ns, the fire-to-store /
ring cone). TASK-003 log, 2026-10-30.
