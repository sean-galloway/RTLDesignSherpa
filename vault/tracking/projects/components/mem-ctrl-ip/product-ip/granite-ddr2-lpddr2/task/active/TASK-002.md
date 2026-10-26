---
title: TASK-002 — bank queues as gaxi_age_fifo_sync; oldest-in-pool is the aged request class
summary: Replace the store's linked-list bank queues with sixteen gaxi_age_fifo_sync instances (PEEK = 2) carrying the pool age, so a head's rd_age_thresh is the record's age_exceed and the pick's aged-first class means "oldest entry in the pool".
---

# TASK-002 — bank queues as gaxi_age_fifo_sync; oldest-in-pool is the aged request class

**State:** active · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-25

## Owner's decision

Owner, 2026-10-25: "at the fire stage, there should be at least one fifo with
rd_age_thresh asserted; these could go directly in the req stage of the
arbiter" -- then, offered the pool-column form or the FIFO form, "Do 1: it is
extremely clean." So the queues ARE the FIFOs.

## What the review found first (the block's writer rule)

`gaxi_age_fifo_sync` (47938c0c3, same morning) documented the pool rule as
`youngest + 1`, or `youngest` with `age_dec`, with no empty-pool case.
`youngest` reads 0 for an empty pool and for a saturated entry alike, so the
first entry into an empty pool landed at age 1 and every later entry inherited
the shift; the test's rank check (`age == rank + 1`) called that correct. A
request stage driven from the thresh bits would never request the first
command into an idle controller (nothing fires, nothing retires, nothing
decrements). Fixed in the header, the doc page, the TB pool driver and its
invariant (`age == rank`, plus "occupied pool => some head has thresh");
mutations `POOL_WRITER_EMPTY_TERM=0` and `POOL_WRITER_DEC_TERM=0` both fail
(the first on the very first entry). FUNC grid 4/4 then 5/5 with PEEK.

Proof the owner's claim rests on (now in the FIFO header and doc): with the
empty term, every live entry's age is at most its rank; the oldest (rank 0)
sits at age 0 at the head of its FIFO; its thresh flop is set in the cycle
after the edge that made it oldest. Conditions: exactly one `age_dec` per
retirement (the pick fires one command per cycle: commit and issue are
exclusive), thresh as a priority term over plain head-valid requests (the
aged head may be timer-blocked), ties at 0 need a tie-break.

## What landed (uncommitted)

- `rtl/amba/gaxi/gaxi_age_fifo_sync.sv`: `PEEK` parameter (entries behind the
  head exposed as `pk_valid / pk_data / pk_age_thresh [PKN]`, modulo DEPTH,
  `PEEK >= DEPTH` does not elaborate). TB checks the peeks every cycle;
  runner grid carries PEEK 0 / 2 / 3 cells.
- `mc_bank_fifo_store.sv`: the linked lists (`next` per slot, head / tail per
  bank, `r_wsp` / `r_rsp`), the shared 16-bit age counter, the per-slot
  stamps and the threshold compare are gone. Per (direction, bank) one
  `gaxi_age_fifo_sync #(DATA_WIDTH = PTRW + 1, AGE_WIDTH = clog2(2N), DEPTH =
  QD, PEEK = 2)`; entry = {same-row-as-previous, slot}. Records read head,
  pk[0], pk[1] directly. Pool age: `age_dec = commit | issue`;
  `wr_data_age = pool_empty ? 0 : any_retire ? youngest : youngest + 1`
  with `youngest` a balanced max tree over the 16 queues' outputs (one array
  per level) and `pool_empty` from the queues' `rd_valid`s (NOT slot
  validity: a committed write slot stays valid while it drains but has left
  its queue). `age_exceed = HAS_AGE && (sched_age_thresh != 0) && thresh`:
  the CSR field is the enable, its magnitude is not read. A registered
  per-bank count stays for the admission bound and `BANK_CAP_MIXED` (the
  FIFO's `count` leads and would loop through the push handshake).
- Filelist `fub/mc_bank_fifo_store.f` includes `gaxi_age_fifo_sync.f`.
- Proxy knob `TEST_AGE_THRESH` in `test_granite_char_perf.py` (needs
  `TEST_HAS_AGE=1`).
- Docs: FIFO page (PEEK, proof, production instance), handbook
  `design/per-bank-queues-admit-from-the-pool.md` (new bullet), store header.

## Verification

- Lint: store standalone 0 warnings; granite_core at HAS_AGE 0 and 1, 0.
- granite dv/tests/top FUNC: 6 passed, 1 xfailed (the pre-marked geared
  8/12 cell), clean build.
- val/amba gaxi_age_fifo_sync FUNC: 5 passed (PEEK 0/2/3), 0 mismatches.
- common-ip fub + macro, clean: first run 5 compile failures -- the macro
  TB's `dv/filelists/mc_store_arbiter_macro.f` hand-lists the store and did
  not carry the new closure; `-f gaxi_age_fifo_sync.f` added. Rerun 30
  passed, 3 xfailed (the pre-marked frfcfs-entry cells). Registry --check
  and --audit PASS.
- Perf proxy A/B, one thread (same harness, head worktree ed3fed31c =
  linked list, vs this text). HAS_AGE 0: CYCLE-IDENTICAL on all four
  families (wr/rd cycles 2162/2157, 2131/2139, 2666/2715, 3949/3427), 0
  mismatched -- the queue form changes nothing on its own. HAS_AGE 1 +
  age_thresh 1 (oldest-first class live):

  | family | list wr/rd MB/s | oldest-first wr/rd MB/s |
  |---|---|---|
  | incremental | 568.2 / 569.6 | 567.7 / 564.6 |
  | row_major | 576.5 / 574.4 | 570.9 / 569.3 |
  | col_ilv | 460.8 / 452.5 | 455.2 / 453.5 |
  | col_major | 311.1 / 358.5 | 310.0 / 357.0 |

  0.1 to 1.2 percent down on the single-thread streams: the oldest head
  outranks the alternation / hint heuristics and costs a cycle here and
  there.
- Eight threads + the mixed family (TEST_NUM_GEN=8). HAS_AGE 0: again
  CYCLE-IDENTICAL to the list on all five families. HAS_AGE 1 + age_thresh
  1 (thresh as the TOP select line, the pick's existing aged-first slot):

  | family, 8 thr | list wr/rd MB/s | oldest-first wr/rd MB/s |
  |---|---|---|
  | incremental | 556.9 / 557.4 | 556.8 / 501.8 |
  | row_major | 557.6 / 557.5 | 557.1 / 500.9 |
  | col_ilv | 533.5 / 543.8 | 535.2 / 495.0 |
  | col_major | 459.7 / 458.5 | 458.9 / 458.1 |
  | mixed (R+W concurrent) | 106.5 combined | 49.3 combined (2.16x cycles) |

  Reads lose 10 percent on the streams and the mixed family HALVES: exactly
  the predicted failure of oldest-first at the top of the select -- it
  outranks the direction register, so with reads and writes both live the
  bus turns around on nearly every pick (tWTR / tRTW each time). This is
  the PLACEMENT of the thresh bits, not the structure: the structure is
  cycle-identical with the class off. HAS_AGE stays 0. The owner's call:
  thresh as the within-class tie-break (ahead of the rotor, after the
  direction / alternation choice) is the form to measure next, and it is a
  pick-core edit (mc_bank_pick select block), which this task has NOT made.
- Board (Nexys A7, 75 MHz, `make bitstream`, HAS_AGE 0 default), whole
  harness: 38 566 -> 39 211 LUT (+645: +453 as logic, +192 as memory --
  the FIFO entry arrays map to distributed RAM), 32 654 -> 32 683 FF (+29),
  WNS +0.177 -> +0.236 ns, 0 failing both. The checked-in
  `utilization_hier*.txt` are STALE (05:56 / 17:17 timestamps; the flow no
  longer writes them -- harness item: build_all.tcl should write the
  hierarchical report again), so the per-block A/B is a synth-level
  `report_utilization -hierarchical` on both trees with the same flow
  (`make synth` in the head worktree vs this build's synth checkpoint):

  | synth, depth 5 | list (ed3fed31c) | age FIFOs | delta |
  |---|---|---|---|
  | u_core granite_core LUT / FF | 5 190 / 3 207 | 4 996 / 3 307 | -194 / +100 |
  | u_fifo_store LUT (logic + LUTRAM) / FF | 2 255 (2 251 + 4) / 1 365 | 2 160 (1 964 + 196) / 1 501 | -95 / +136 |

  Routed, this build: u_core 4 871 LUT / 3 296 FF, store 2 089 / 1 501.
  The FIFO entry arrays go to LUTRAM and the list's pointer-chasing muxes
  go away; the age / thresh flops are folded out at HAS_AGE 0, the valid
  masks and pointers remain. The whole-harness +645 LUT above is therefore
  NOT the store (u_core is down): per-block attribution shuffles across the
  unchanged planes between builds (handbook: area-measure-by-hierarchy),
  report u_core.

## Result (2026-10-25 evening)

Structure: in. Cycle-identical to the linked list with the class off at 1 and
8 threads, smaller at u_core (-194 LUT, +100 FF), timing +0.236 ns. Policy:
thresh at the top of the select is measured and rejected (mixed halves,
stream reads -10 percent at 8 threads); HAS_AGE stays 0 pending the
within-class placement, which is the owner's call on the pick core.

## Timing inside the controller (routed checkpoints, 2026-10-26)

The harness WNS (+0.177 -> +0.236 ns at 75 MHz) says little on its own: both
builds are bounded by the char-engine register block, not the controller.
The controller-only view, from `report_timing -cell u_core` on the routed
checkpoints, is the number that moved:

| worst path inside u_core          | linked list (2026-10-24 build) | age FIFOs |
|-----------------------------------|--------------------------------|-----------|
| slack                             | 0.340 ns                       | 0.934 ns  |
| path                              | pick `r_pick_pair` -> store `r_wsp` (pointer chase) | pick `r_hold` -> pick `r_pick_cls` |
| worst path inside the store       | 0.340 ns (the same path)       | 0.980 ns, pick `r_hold` -> `u_rq/r_valid` |

The linked list's pointer-chase path was rank 8 of the whole design in the
old build; the new build has no controller path in the design's worst 20
(the 20th-worst slack moved 0.450 -> 0.789 ns). The new controller-worst path
is 79 percent route, so a second seed will move it, but 0.34 -> 0.93 ns is
outside run-to-run noise. The harness-level reports under
`targets/granite/fpga/reports` were NOT committed with this change: that
build also carried the uncommitted pumice TASK-060 char-framework edits in
the harness, so its numbers are not reproducible from this commit alone.

## Risk to measure, not argue (written before the numbers; kept)

With thresh as the aged class, the oldest pool entry is always "aged", so
the arbiter's first select line serves the oldest fireable head every cycle
and overrides the ACT/column alternation and the direction batching. If the
oldest alternates direction the bus turns around on every pick (tWTR/tRTW).
The alternative is thresh as the tie-break inside each class. HAS_AGE stays
0 as the product default until the A/B says otherwise.
