# TASK-011: build generator patterns that can show RBL a win

**Status:** CLOSED 2026-09-25 — board run done. mode 6 is strictly worse than mode 7; mode 7 is bit-identical to no predictor. RBL does not earn its 5,578 LUT. **Priority:** P3 — research capability; no
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


## 2026-09-25 — BUILT, and the workload discriminates. RBL does not win.

`hotcold_scenarios()` + a `same_bank` placement + the `rbl_hotcold` profile.
Four generators on **bank 0, rows 0-3**: three row-confined against one
striding rows, all readers (see below).

**Sim, board geometry, corrected workload:**

| config | rd %peak | hit% | ACT/txn | PRE | thrash% |
|---|---|---|---|---|---|
| open_page | 31.6% | 74.2% | 4.12 | 33 | **100.0%** |
| rbl_static | 28.9% | 67.2% | 5.25 | 31 | **73.8%** |
| rbl_dyn | 27.8% | 64.1% | 5.75 | 29 | **63.0%** |

**The mechanism is confirmed, for the first time.** thrash% falls 100% -> 63%
and PRE falls 33 -> 29: RBL IS converting conflict-ACTs into empty-ACTs,
exactly as predicted. No uniform workload could move that number at all, which
is the whole point of this task.

**RBL loses the trade anyway.** ACT/txn RISES 4.12 -> 5.75 and hit% falls
74.2% -> 64.1%. It saves precharges on cold rows and spends more activates on
hot ones -- it is over-precharging, closing rows that should have stayed open.

**Do not conclude from the sim run.** `reset_interval` is 256 cycles and sim is
8 transactions per generator, so `rbl_dyn` cannot complete a SINGLE epoch --
the adaptive mode is measured with its adaptation switched off, which is
precisely the mechanism [[TASK-010]] credits for keeping it out of
`rbl_static`'s collapse. The board at txn_scale ~1000 is the run that decides
it, and the cheap question ("is mode 6 subsumed by mode 7") cannot be answered
until then.

### Two construction bugs, both caught before the board

Recorded because each would have produced a confident WRONG answer, and each
looked right in the table.

1. **The hot generators were not hot.** They inherited the caller's family
   (`incremental`), whose `strides_for` wrap is **0** -- meaning NO wrap, a
   contiguous march. Intersected with the placement mask that became a walk
   over the whole BANK, touching every row once: the exact uniformity this
   workload exists to break. Hot is now forced to `row_major`, which
   `strides_for` defines as "wrapped inside one page -> every burst a page
   HIT".
2. **The four generators were on four DIFFERENT banks.** On this geometry
   `bank_stride == page_bytes == 0x800`, so stepping a page steps a BANK --
   gen0..3 landed on banks 0,1,2,3. Separate banks share no open row, so the
   cold engine could never evict a hot one and the result would have read "RBL
   does nothing" for a reason having nothing to do with RBL. Now steps
   `geom.row_stride_same_bank` (0x4000), which holds the bank and advances the
   row.

The first table taken (thrash 100% -> 9.9%) had BOTH bugs and is discarded.

### One deviation from the plan, deliberate

The task says four generators in one direction. It specifies WRITES; this uses
**4 readers, 0 writers**. `measure_concurrent` validates through the read
engines -- its pre-fill writes each reader's region first -- so 4w+0r reports
"read engines did not complete" and every row comes back ok=N. 0w+4r keeps the
single direction the task asks for (no tWTR/tRTW turnaround introduced) AND
stays integrity-checked.

Verified: component gate COMP_RC=0 at BOTH geometries; char board gate
CHAR_RC=0, 216 passed 2 xfailed.

**Board run still owed** -- that is what decides mode 6 vs mode 7.


## 2026-09-25 — BOARD RESULT. RBL does not earn its area. CLOSING.

**Silicon, txn_scale=1000 (32k ACTs -- real statistics), peak 600 MB/s:**

| config | rd MB/s | % peak | hit% | ACT/txn | ACT | PRE | thrash% |
|---|---|---|---|---|---|---|---|
| open_page | 195.2 | 32.5% | 87.4% | 4.03 | 32,224 | 32,224 | 100.0% |
| **rbl_static** | **144.2** | 24.0% | 78.5% | **6.88** | **55,051** | 32,076 | 57.8% |
| **rbl_dyn** | 195.2 | 32.5% | 87.4% | 4.03 | 32,223 | 32,223 | 100.0% |

**`rbl_dyn` is bit-identical to plain open page** -- same bandwidth, same hit
rate, 32,223 vs 32,224 ACTs. Its per-epoch hill-climb has driven the threshold
to "never close early": **the adaptive mode adapts itself into a no-op.** That
is the mechanism working correctly -- it detected that early precharge was
hurting and backed all the way off -- but the result is that mode 7 is
indistinguishable from not having the predictor at all.

**`rbl_static` actively hurts: -26% bandwidth.** The mechanism is visible and
behaves exactly as this task predicted -- thrash falls 100% -> 57.8%, i.e.
conflict-ACTs become empty-ACTs -- but it pays **+22,827 ACTs** (32,224 ->
55,051) to do it while PRE barely moves (32,224 -> 32,076). The precharge
saving never materialises; the activate cost does.

### The verdict this task existed to reach

On the workload built specifically to suit it, with per-row locality variation
no uniform pattern could provide:

* **mode 6 is strictly worse than mode 7** -- the "cheap question" this task
  said to answer first, answered.
* **mode 7 is indistinguishable from no predictor.**
* RBL's **5,578 LUT** ([[TASK-005]]) buys nothing here, and mode 6 buys
  negative.

That is a real research result, not a null one: the predictor's mechanism
demonstrably works (thrash moves), and it still loses because the ACT it spends
exceeds the PRE it saves. A per-row predictor on this controller needs the
precharge it avoids to be worth more than the activate it forces, and at BL4
x16 on a bank with one open row, it is not.

**Recommendation for [[TASK-005]]:** mode 6 should be considered for removal --
it is dominated by mode 7 on every workload measured, including this one.
Mode 7 is defensible as a safety property (it cannot hurt) but has yet to show
a win on any traffic.

Verified: 3/3 points passed integrity; component gate COMP_RC=0 at BOTH
geometries; char board gate CHAR_RC=0.
