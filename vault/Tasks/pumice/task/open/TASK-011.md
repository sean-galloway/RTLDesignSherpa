# TASK-011: build generator patterns that can show RBL a win

**Status:** open 2026-09-24  **Priority:** P3 — research capability; no
correctness impact and nothing on the board depends on it

Sean 2026-09-24: *"I believe this could be done across 4 generators, that are
offset from each other but hitting the same bank. 3 could be 'hot' and one
could be 'not'. This is a research memory controller; it is all about
researching theoretical traffic. We could look for traffic that matches what is
good for the mode later."*

Split out of [[TASK-010]], which establishes WHY no current workload can do
this. This task is the construction.

## The workload

Four generators in one direction, all targeting the SAME bank, offset from each
other:

- **3 "hot"** — each confined inside one row (`stride_0` = beat, `wrap_mask_0`
  = row span), so its row is worth holding open.
- **1 "cold"** — striding ACROSS rows in that bank, so each of its rows is
  touched once and is worth closing immediately.

4 wr + 4 rd generators are BUILT (confirmed on the board via `seq_genshape`:
`{'num_wr_gen': 4, 'num_rd_gen': 4, 'num_banks': 8}`), so this needs no
rebuild. Keep all four in one direction: mixing read and write adds tWTR/tRTW
turnaround, which is a second variable and not the one under test.

## Why this is the workload RBL needs, mechanically

A DRAM bank holds **one open row**. With a cold generator walking rows in the
same bank as three hot ones, every hot access after a cold access finds the
bank open on the WRONG row -- a conflict, costing PRE + ACT. If RBL classifies
the cold rows as low-locality and auto-precharges them, the next hot access
finds the bank CLOSED instead: an empty, costing ACT only.

**So the predicted benefit is one precharge per cold access**, and it is
directly observable rather than inferred: `PAGE_STATS_MISS` counts
conflict-ACTs and `PAGE_STATS_EMPTY` counts cold-ACTs, both surfaced as
`thrash%` by the [[TASK-006]] telemetry. RBL winning looks like thrash% falling
while ACT/txn holds -- not merely a bandwidth number moving.

A single generator cannot produce this. `dma_address_gen` is 2D affine
(`base + i0*s0&w0 + i1*s1&w1`) and affine is uniform across rows by
construction: confine the inner index to a row and every row gets identical
traffic. The variation has to come from generators programmed DIFFERENTLY.

## What to build

1. **Per-generator Scenario override in `measure_concurrent`.** Today
   `_prog(idx)` derives everything from one `Scenario` and only `start_addr`
   varies, so N generators are N copies. Take a list, defaulting to the current
   single-scenario behaviour so every existing profile is unaffected.
   `program_wr_engine`/`program_rd_engine` already accept `gen=N` with full
   per-generator stride/wrap, so this is host-only -- no RTL, no rebuild.
2. **A `rbl_hotcold` profile** on the shape above, swept across `open_page`,
   `rbl_static`, `rbl_dyn`.
3. Report thrash% and ACT/txn beside bandwidth, per [[feedback_bandwidth_tables_need_peak]] —
   and expect ABSOLUTE numbers in the page-hostile range (~100-250 MB/s against
   the 600 MB/s ceiling), because that is the corner where a per-row predictor
   can pay. The comparison that matters is between MODES on identical stimulus,
   not against peak.

## Answer the cheap question first

[[TASK-010]] notes that `rbl_dyn` does not exhibit the `rbl_static` pathology
(97.8 vs 55.8 MB/s on the same concurrent stimulus, three reps) because its
per-epoch hill-climb walks the threshold away from a mispredicting value. If
mode 7 is strictly better than mode 6 on every workload including this one,
then the useful outcome is "mode 6 is subsumed by mode 7", and that is worth
knowing before investing in a workload built to flatter mode 6.

**Framing, recorded because it is the point:** pumice is a RESEARCH controller.
The question here is not "does real traffic look like this" -- it is what the
mechanism can do on traffic constructed to suit it. Matching that back to real
workloads comes later, and is a separate question.
