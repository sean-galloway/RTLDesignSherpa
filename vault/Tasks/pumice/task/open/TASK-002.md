# TASK-002: characterize + tune the advanced modes (all three axes)
> **Was `PUMICE-013` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-08-27. AXIS 1 SWEPT ON SILICON 2026-09-25 (8/10 sub-policies inert; row_most_pending -19.4%). Axes 2/3 tuning still open. Originally: FIRST CAMPAIGN LANDED 2026-09-23 — all three axes
swept one-at-a-time on the board, results and recommended defaults in
"TASK-002 RESULTS" below. Four mechanism gaps reported to [[TASK-001]],
one of them a shipped RTL default that costs 15.8x on streaming. Still open
for the axis PAIRS, the axis-3 re-run under open page, and the scheduler
sub-knobs that were not reached (listed under "What is NOT yet characterized").
(split out of TASK-001 at Sean's direction —
"move characterization to its own task as that is a big one")

TASK-001 delivered the MECHANISMS: every mode of all three axes is
implemented, OFF by default (encoding 0 = build default, bit-identical),
and mutation-proven at the fub level. What it deliberately did NOT do is
answer *which settings are actually good* on real traffic. That is this
task, and it is a large body of work: a mode-cross characterization
campaign in sim and on the board, plus the tuning defaults that come out
of it.

**The surface to sweep** (all runtime CSR, no rebuilds):
- **Axis 1 (scheduling)** — `SCHED_POLICY.order_mode` (in_order /
  fr_fcfs / age_threshold + `age_thresh`), `row_sel` / `col_sel`
  (oldest / most_pending / fewest_pending), `access_pref` (column /
  row / precharge first), `prio_sub` (load_over_store / none /
  age_boost), `qos_en`, and `SCHED_WR_WM.wr_high_wm/wr_low_wm`.
- **Axis 2 (paging)** — `PAGE_POLICY_CFG.policy_mode` 1..7 with
  `PAGE_TIMEOUT_CFG` (fixed_open/adapt_time TR bounds + step),
  `PAGE_ADAPT_CFG` (MC thresholds, check interval),
  `PAGE_POLICY_CFG.ctr_open_max/ctr_init` (adapt_access), and
  `PAGE_RBL_CFG` (miss threshold, ways/sets, epoch).
- **Axis 3 (refresh)** — `REF_CTRL.mode` (REFab / refpb_rr),
  `postpone_limit` / `pullin_limit`, `REF_TIMING_PB` (tREFIpb, tRFCpb).

**What makes this big (and why it is not just "run the matrix"):**
1. The cross is combinatorially large — sweep one axis at a time against
   a fixed baseline first, then the promising pairs; do NOT brute-force
   the full product.
2. NO LONGER A GATE (2026-09-23). This read "land [[PUMICE-016]] first or
   the numbers carry the AMBA-HISTCH1 accounting error". 016 is DROPPED:
   the harness meters are the shared primitives, not bespoke, and the
   AMBA-HISTCH1 accounting error was fixed at source (44ba2eea3) rather
   than by retiring them. The 1:1 check is measured clean at board
   geometry -- multiid hist total 64/64. Nothing blocks this work.
3. DONE 2026-09-23 (226d8cf68). The in-controller telemetry is now READ
   by the host -- it never was; `grep hit_rate` across all three tiers was
   empty, so two of the four deliverables were unreportable. PAGE_STATS /
   SCHED_STATS / REF_STATS now land in every CharRecord as a per-phase
   delta and print in the table. Three traps documented in the PageStats
   docstring: PAGE_STATS_HIT counts EVERY column op (not hits), the
   counters free-run so they must be diffed, and the hit-rate scale is
   floored by burst length (87.5% on the board's BL4) -- compare
   `rd_acts_per_txn`, not the rate. OBS_ROW_HIT per bank and the
   refresh-defer histograms are still unread.
   [[PUMICE-015]] (greppable structure trackers) is the sim-side
   companion for understanding *why* a setting wins.
4. Board and sim disagree by construction — the DFI loopback models no
   page timing, so ordering/paging wins only show up on silicon or
   against a timing-faithful model. Sim runs prove mechanism + integrity;
   the board run produces the numbers.

**Deliverables:** a per-axis sweep report (BW, latency histogram, page
hit rate, ACT/PRE/REF counts per setting), recommended defaults per
workload family (streaming / random / mixed / page-hostile), and any
mechanism gaps found reported back to TASK-001 before it closes.

**Stimulus + measurement that already exists (audited 2026-08-27):**
- `pumice_char.py` families ARE the paging grade: `row_major` is
  contiguous WRAPPED INSIDE A PAGE (every burst a HIT), `col_major` walks
  rows in one bank (every burst a MISS), `incremental` marches
  contiguously (hits until each row crossing). row_major reaches sim via
  the `matrix`/`full` profiles; `smoke` only crosses incremental +
  col_major, so the hit case is missing from the quick profile.
- Sim tests have page-hit stimulus but do NOT grade it: `row_hit_pattern`
  walks columns in one {bank,row} (all hits, 6/16/32 bursts, data-only
  check); `engine_mirror` streams contiguous bursts but runs
  page_policy=CLOSE by design, so it is a throughput test, not a paging
  one. NOTHING reads PAGE_STATS -- `grep hit_rate` across all three
  tiers is empty.
- NEW: `AxiChanTracker` (PUMICE_TRACKERS=1) writes `axi_util.out` with
  per-channel utilization in axi_bus_meter buckets + handshake run
  lengths. MEASURE ON THE BFM TOP TB (masters at the `backtoback`
  randomizer profile), never the hand-driven core TB -- Sean 2026-08-27:
  "set the masters delay profile at b2b, this is the only meaningful way
  to test this".
  MEASUREMENT (top engine_mirror N=1024, backtoback, 62135 cycles):
    chan   util%   bp%   starv%  max_run  runs
    axiaw   1.65   0.0    98.35        1  1024 x1
    axiw    6.59   0.0    93.41        1  4096 x1   <-- writes NEVER stream
    axib    1.65   0.0     0.05        1  1024 x1
    axiar   1.65   0.0    98.35        1  1024 x1
    axir    6.59   0.0    50.36        4  1023 x4   <-- reads hold a full burst
  Self-consistent (axiar 1024 == camrd 1024 INSERTs; axiw 4096 == 1024
  bursts x 4 beats), so these are trustworthy.
  TWO FINDINGS worth chasing in this task:
  (a) the W channel's max_run is 1 -- write data beats never go
      back-to-back even with a zero-delay master, while R sustains a
      full 4-beat burst. Worth understanding before any write-side
      perf claim.
  (b) bp=0% everywhere with ~60 cycles/burst means the DUT never
      stalled the master: the remaining limiter is OUTSTANDING DEPTH
      (one burst in flight), not inter-beat delay. Fixing the delay
      profile was necessary but not sufficient -- a driver that waits
      for each completion still starves the DUT.

**Existing collateral to build on:** `pumice_char.py` (families,
RUN_PROFILES, the `multiid_min` repro profile), `pumice_master.py --char`
with `--char-configs` / `--char-level` / `--char-scale`, and the board
recipe in [[project_pumice_board_perf_char]] (the runtime page-policy
result — OPEN giving 8.8x on streaming, 12.7 -> 112 MB/s — is the
template for what a good characterization finding looks like).

---

### TASK-002 RESULTS -- board campaign 2026-09-23

Run on the Nexys A7 at 75 MHz, existing 2026-09-21 bitstream (no rebuild: the
telemetry counters predate it by a month). `run_smoke.py --sequences init char`
over the `paging_grade` / `paging` / `order` / `refresh` profiles at
`--txn-scale 1000` (txn_count 8000, 512 KB moved per scenario), plus a focused
`rbl_epoch` sweep. Every point `ok=True`, 0 beats mismatched.

The in-controller telemetry that makes this a characterization rather than a
scoreboard landed first (226d8cf68): nothing on the host had ever read
PAGE_STATS / SCHED_STATS / REF_STATS. Read the PageStats docstring before
quoting any number from these tables -- the hit-rate scale has a floor that
moves with burst length, which is why ACT/txn is the column to compare modes on.

### Axis 1 -- scheduling order

| config | order_mode | page | incremental | col_major | ACT/txn (inc) |
|---|---|---|---|---|---|
| open_page | fr_fcfs (0) | OPEN | **554.1** | **163.8** | 0.05 |
| age_thr | age_threshold (3) | OPEN | **554.1** | **163.8** | 0.05 |
| inorder_open | in_order (1) | OPEN | 142.1 | 94.2 | 0.09 |
| inorder | in_order (1) | CLOSE | 34.0 | 33.9 | 8.17 |

- **age_threshold is FREE.** Bit-identical to fr_fcfs on both families -- same
  bandwidth, same ACT (368 / 8399). At `age_thresh=8` the starvation bound
  never fires on this traffic, so it costs nothing and buys a bound.
  **Recommended default.**
- **In-order costs 3.9x on streaming** (554.1 -> 142.1) and 1.7x on
  page-hostile (163.8 -> 94.2). That is the price of giving up reordering,
  measured at equal page policy.
- **`inorder` is a confounded datapoint** -- the CONFIGS entry pairs
  order_mode=1 with CLOSE page, so its apparent 16x deficit is mostly the page
  policy. Compare `inorder_open` vs `open_page`; the raw `inorder` row will
  mislead anyone reading the order axis.

### Axis 2 -- paging

Open vs close, the headline: **16.3x on streaming** (554.1 vs 34.0), **4.8x on
page-hostile** (163.8 vs 33.9). Close page pays 8.17 ACT/txn -- one activate
per column op -- for a 0.0% hit rate on every family.

| predictor (all on OPEN page) | incremental | col_major | vs plain open |
|---|---|---|---|
| plain open_page | 554.1 | 163.8 | -- |
| adapt_time (mode 4) | 554.1 | 163.8 | identical |
| adapt_access (mode 5) | 554.1 | 163.8 | identical |
| rbl_dyn (mode 7, epoch 256) | 549.7 | 163.8 | -0.8%, +33 ACT |
| rbl_static (mode 6, epoch 0) | **34.9** | 163.8 | **-15.9x** |
| rbl_static AFTER the fix (epoch 256) | 554.1 | 163.8 | identical |

- **No predictor beats plain open page on these workloads.** adapt_time and
  adapt_access are free but inert here; rbl_dyn is marginally worse.
- **rbl_static collapses streaming to close-page behaviour.** 34.9 MB/s, 0.0%
  hit, 8.17 ACT/txn -- byte-for-byte the close-page numbers. See the mechanism
  finding below.

### Axis 3 -- refresh

| config | incremental | col_major | ACT/txn | PRE |
|---|---|---|---|---|
| slow_refresh (tREFI 0x7FFF) | **36.3** | **35.3** | 8.00 | 0 |
| baseline (tREFI 585) | 34.9 | 33.9 | 8.16 | 1312 |
| refresh_credit (postpone/pullin 8) | 34.9 | 33.9 | 8.16 | 1314 |
| fast_refresh (tREFI 256) | 33.7 | 32.7 | 8.27 | 2134 |

- Refresh interval spans **~8% fast-to-slow**. slow_refresh reaches exactly
  8.00 ACT/txn with **PRE=0** -- no refresh-induced precharges at all.
- **`refresh_credit` has no measurable effect** on this traffic (34.9/33.9,
  within noise of baseline, ACT within 2).
- **CAVEAT, and it limits the axis:** all four refresh configs pin CLOSE page,
  so refresh is measured in the ~34 MB/s regime where it matters least. Refresh
  interference should be re-measured under OPEN page at ~554 MB/s, where the
  same absolute stall is a far larger fraction. The config table needs
  open-page refresh variants before axis 3 can be called characterized.

### Recommended defaults per workload family

| family | recommendation | measured |
|---|---|---|
| streaming (incremental, row_major) | open page + fr_fcfs **or** age_thr | 554-569 MB/s |
| page-hostile (col_major) | open page + fr_fcfs; bank-interleave the map | 163.8 -> 229.3 MB/s |
| mixed / latency-sensitive | open page + age_thr (free starvation bound) | 554.1 MB/s |
| any | **never** rbl_static at the default epoch; in_order only if ordering is required | -- |

### Mechanism gaps -> [[TASK-001]]

1. **`PAGE_RBL_CFG.reset_interval` defaults to 0 = "never" and that default is
   unusable on streaming.** RTL reset default is `16'h0` (pumice_csr.rdl:716).
   With counters that never decay, the RBL predictor latches closed on
   streaming traffic and cannot relearn. Isolated by sweeping only that field
   (`seq_rbl_epoch`, reproduced twice):
   `epoch 0 -> 34.9 MB/s / 0.0% hit`; `epoch 1, 16, 64, 256 -> 553.4-553.8 /
   99.4%`; `epoch 1024 -> 207.2 / 88.2%`. **15.8x, and ANY nonzero epoch
   repairs it.** col_major is 163.8 at every epoch -- it genuinely misses, so
   the predictor is correct there, which is exactly why a col_major-only sweep
   could not have found this. Recommend a nonzero reset default in [16, 256].
2. **`CONFIGS["inorder"]` confounds order_mode with page policy** (see axis 1).
3. **Axis-3 configs all pin CLOSE page** (see axis 3).
4. **REF_STATS_REF is not window-attributable from the host.** It free-runs on
   tREFI, so a host-bracketed delta times the UART round trips: a 186 us window
   measured a raw delta of 61446 (479 ms implied, 2584x). Fixed host-side in
   71c4fb030 -- the table reports window_cycles/tREFI and flags contamination --
   but a windowed/clearable refresh counter in RTL would make axis 3 directly
   measurable instead of estimated.

### What is NOT yet characterized

The sweeps above are one-axis-at-a-time against a fixed baseline, which is what
the task prescribes. Not done: the promising PAIRS (order x paging, paging x
refresh), the `SCHED_WR_WM` write-batching interaction (ISSUE-004 has its own
board number to re-measure), `prio_sub` / `qos_en` / `row_sel` / `col_sel`,
and the axis-3 re-run under open page. There is also no genuinely RANDOM family
-- `col_major` is the page-hostile proxy -- so "random" in the workload table
above is not directly measured.


### PAIR SWEEPS 2026-09-24 — the two the campaign was missing

Two new profiles, both on the board at txn_scale=1000, every point ok.

**Pair 1: paging x DIRECTION MIX** (`pairs_paging_mix`, concurrent 1w+1r). The
single-axis campaign swept steady-locality families one at a time, where a
predictor has nothing to predict. A concurrent read/write stream is the closest
this harness gets to ALTERNATING locality: the two directions interleave and the
row a reader wants is not the row the writer just opened.

Result: **every predictor is identical to plain open page on 3 of 4 scenarios**
(incremental 274.3 vs 274.7, row_major 284.0, col_major 79.8 — all within
noise). And one is a large REGRESSION:

| rep | open_page / col_major_interleaved | rbl_static / same |
|---|---|---|
| 1 | 98.3 MB/s, 81.3% hit, 3.00 ACT/txn | **55.8 MB/s, 44.0% hit, 8.96 ACT/txn** |
| 2 | 98.3, 81.5%, 2.96 | 56.0, 44.2%, 8.93 |
| 3 | 98.3, 81.3%, 3.00 | 55.7, 43.9%, 8.97 |

**-43%, reproducible to +-0.3 MB/s across three independent runs.** The hit rate
halves and ACT/txn triples: the RBL predictor decides the interleaved rows are
low-locality and auto-precharges rows that the OTHER direction was about to
reuse. It is wrong in exactly the situation it exists for. Repeated three times
on purpose -- [[BUG-001]]'s lesson is that this area has twice decided a default
at n=1.

**Pair 2: refresh x OPEN page** (`pairs_refresh_open`). Axis 3 had only ever been
measured under CLOSE page at ~34 MB/s, where refresh is a small slice of a slow
run. On the page policy the board ships:

| config | incremental | row_major | col_major |
|---|---|---|---|
| open_page (tREFI default) | 553.9 | 568.9 | 163.8 |
| refresh_credit_open | 556.2 (+0.4%) | 572.4 (+0.6%) | 164.1 |
| fast_refresh_open (tREFI 256) | 516.2 (**-6.8%**) | 529.6 (**-6.9%**) | 156.4 |
| slow_refresh_open (tREFI 0x7FFF) | 569.3 (+2.8%) | **599.0 (+5.3%)** | 171.3 |

Two things worth keeping:

1. **Refresh costs 2.8-5.3% of streaming bandwidth at the default tREFI**, and
   the fast-to-slow span is ~16% (516 -> 599). Under close page the same span
   read ~8% of a 34 MB/s number; this is the version that matters.
2. **`slow_refresh_open` / row_major reaches 599.0 MB/s at a 100.0% hit rate,
   ACT=3 for the whole run.** Theoretical peak is 600 MB/s (8 B x 75 MHz), so
   pumice is at **99.8% of peak** with refresh effectively disabled. Refresh is
   the only remaining gap between this controller and its ceiling on streaming
   reads -- not the scheduler, not the page policy, not the front end.

`refresh_credit` is +0.4-0.6%, which is within run-to-run noise: still no
measured effect, now established on the policy where one was plausible.


## 2026-09-25 — AXIS 1 SUB-POLICIES MEASURED ON SILICON. Eight of ten are inert.

The axis was never swept because `ControllerConfig` did not expose it:
`prio_sub` / `row_sel` / `col_sel` / `access_pref` / `qos_en` are SCHED_POLICY
fields the driver has always accepted and `apply()` never programmed -- so they
INHERITED across the matrix, the same order-dependence hazard recorded here for
`refresh_credit` (574 MB/s purely because it ran after `rbl_dyn`). Now
programmed on EVERY config, with 9 single-lever configs and a `sched_sub`
profile.

**Board, txn_scale=1000, single direction (0w+4r), peak 600 MB/s:**

| config | incremental | col_major |
|---|---|---|
| open_page (default) | 194.5 | 195.2 |
| **row_most_pending** | **196.6 (+1.1%)** | **157.4 (-19.4%)** |
| pref_row_first | 195.1 (+0.3%) | 195.2 (0.0%) |
| row_fewest_pending | 193.9 (-0.3%) | 195.2 (0.0%) |
| prio_load_over_store, prio_age_boost, col_most_pending, col_fewest_pending, qos_on, pref_column_first | 194.5 (0.0%) | 195.2 (0.0%) |

**Eight of ten sub-policies are within +-0.3% of the default -- inert on this
traffic.** `row_most_pending` is the only lever with real effect and it is a
net LOSS: +1.1% on sequential, **-19.4% on page-hostile**, where it also costs
+7,300 ACTs (78,213 -> 85,552). Its 2+2 run showed rd_lat 244.8 -> 593.7, a
2.4x latency penalty.

Provisional read: the default (oldest-first) is the right choice on both
families, and the row arbiter's "most pending" heuristic actively fights the
page policy -- it picks the bank with the most queued work rather than the one
whose row is already open.

### Getting a measurable workload took two corrections

**1. The first sweep was turnaround-bound, not arbiter-bound.** At concurrent
4w+4r the board reports `limiter=turnaround`: traffic switches direction
constantly and tWTR/tRTW dominates. An arbiter sub-policy chooses WHICH
COMMAND, not which direction, so nothing it does can move a workload bound by a
global DQ constraint -- the sweep read flat for a reason that was not about the
knobs. `sched_sub` is single-direction now.

**2. `max_outstanding=32` was a no-op.** 0 already means "as built" =
GEN_MAX_OUTSTANDING = 32, the ceiling. The engines were always saturated on
that axis; the ACT rise 32k -> 79k came from 4w+4r alone.

### Instrumentation added, and one column that was wrong

`measure_concurrent` never captured stall attribution -- only `measure()` did
-- so EVERY concurrent profile (sched_sub, rbl_hotcold, concurrent, multigen,
both pair sweeps) has been blind to its own limiter since it was written. Now
captured, with `limiter` and `blk_cyc` columns.

`limiter` ranks the SIX trustworthy counters and deliberately excludes
STALL_NOREQ, which advances during host UART time exactly as REF_STATS_REF did
before [[TASK-012]]. A first cut ranked noreq with the rest and printed
`starved / 98.8%` for every cell -- that number was timing the HOST, and
presenting it as a property of the run would have retired this axis on an
artifact. The second cut divided blocked cycles by `rd_cycles` and printed
**109.6%**, visibly impossible, which is the only reason it was caught: the
pumice counters are cleared only by aresetn (harness `clear_stats` touches the
bus meters, not these), so a host-bracketed delta spans the window plus
trailing UART time, and `rd_cycles` counts one direction. `blk_cyc` is now an
absolute count -- comparable ACROSS ROWS of one sweep, not readable as a duty
cycle.

**Still open:** axis 2 (paging) and axis 3 (refresh) tuning, and the random
family. Axis 3 is measurable for the first time via REF_STATS_REF_BUSY
([[TASK-012]]), which reads 8,814 against 2,570,069 free-running on silicon --
a 292x contamination factor.
