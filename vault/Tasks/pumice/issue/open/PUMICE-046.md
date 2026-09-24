# PUMICE-046: close-page modes reach only ~63% of their own command-bus ceiling

**Status:** open 2026-09-20  **Priority:** P2 — invisible at the sim geometry,
dominant at the board's, and it caps close-page paging on silicon

Found while making the paging assertions geometry-aware for [[PUMICE-028]].
The arbiter issues at most ONE DFI command per cycle, so no mode can exceed
`BL_WORDS / commands_per_access` beats per cycle. Measured at board geometry
(`TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16`), 8-bank rotation,
refresh parked:

| mode | cmds/access | ceiling | measured | of ceiling |
|---|---|---|---|---|
| build_default / fixed_open | 1.04 | 96.0% | 98.97% | at it |
| static_open / adapt_time | 1.08 | 92.3% | 95.05% | at it |
| adapt_access | 1.09 | 91.9% | 92.75% | at it |
| **static_close / rbl_static** | **2.04** | **49.0%** | **30.77%** | **63%** |
| **rbl_dyn** | **1.64** | **61.0%** | **32.32%** | **53%** |

Every open-page mode sits at its ceiling. The close-page family does not, and
the shortfall is **command scheduling, not DRAM timing**:

- `static_close` measures **30.77% at tRRD 1, 2 AND 4 alike** -- inter-bank ACT
  spacing is not the limiter, which was the obvious first theory and is wrong.
- Only tRCD moves it, and only partway: 37.35% at tRCD=1, 37.5% with tRCD=1,
  tRP=1 and tRC=2 together. Even with every row timing at minimum it is 2.67
  cycles/access against a 2.04-command access.
- So ACT and WR are not being overlapped across the 8 banks as tightly as the
  command bus permits -- roughly 1.2 cycles/access of scheduling slack.

**Why it was never seen:** at the sim geometry BL_WORDS=4, so a 2-command
close-page access has a ceiling of 4/2 = 2.0, clamped to 1.0. The AXI side
saturates first and the inefficiency is entirely hidden behind 2x of headroom
-- `paging_sweep` reads 100% for every mode and passes. At BL_WORDS=1 (the
board) there is no headroom and it is the dominant term. This is the same
lesson as [[PUMICE-028]]: a suite that cannot express the shipping geometry
cannot see what the shipping geometry exposes.

**Reproduce:** `TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16 pytest
top/test_pumice_core_dfi.py -k 'perf_paging_sweep'` -- the test now asserts
against the measured per-mode ceiling and reports cmds/access, so the gap is
the failure message rather than something to re-derive. `perf_paging_sched_cross`
shows the same thing on 24 of 80 combinations, all `static_close` / `rbl_static`.

**Worth knowing before fixing:** the board runs open-page by default, so this
is not a shipping regression -- it bounds what close-page paging could ever be
worth, and [[PUMICE-013]] (characterize + tune the advanced modes) should not
quote close-page numbers until it is resolved or accepted.

### 2026-09-21: root-caused; partially fixed; residual is ACT->column latency

**Cause of the drain.** The classify-time ACT mask gated on `tfaw_ok_i` and
`trrd_ok_i`. Both are GLOBAL (not per-bank), so the instant tRRD closed every
ACT candidate vanished, the 3-stage pick pipeline drained completely, and it
cost 3 more cycles to refill once the gate reopened. Under CLOSE page that is
an ACT per access: the stream ran 6 commands then stalled 5 cycles, an
11-cycle period for 3 accesses. Probed directly -- `actm` collapses to 0 on
`rrd0` while the CAM is full (`v8`) and banks are act-ready, then the masks
repopulate two cycles before the first pick returns, which is the refill.

The gate is REDUNDANT for correctness: `w_act_gate_live` re-checks tRFC/tFAW/
tRRD live at the fire stage (4a/4b) and that check is authoritative. Removed
it there, keeping the fire-stage check. The pick classes are separate pipeline
registers chosen by priority at the output, so an ACT waiting on tRRD does not
block a column.

| mode | before | after |
|---|---|---|
| rbl_dyn | 32.32% | **41.56%** (+29%) |
| build_default / fixed_open | 98.97% | 99.48% |
| adapt_access | 92.75% | 93.66% |
| static_open / adapt_time | 95.05% | 95.52% |
| static_close / rbl_static | 30.77% | **30.77% (unchanged)** |

**One regression, found and contained.** With candidates now flowing during
the tRRD window, ACTs win slots that the drained pipeline used to leave to
columns -- and `pref_row_first` is ACT-beats-COL by definition, so it fell
from ~80% to 72.45% at the DEFAULT geometry, under its 75% floor. Qualifying
the ACT class with the live gate did NOT fix it, which rules out a wasted
output slot: the ACTs genuinely arrive earlier now. Since the board runs
column-first and row_first's arbitration is a characterized PUMICE-013 result,
the classify gate is RETAINED under row_first only (`w_act_classify_gate`)
rather than re-tuning that floor. Default geometry is 18/18 again.

**Why static_close did not move, and what is left.** From the DFI command
trace: `ACT@130 ACT@136 ACT@140 ... WR@170` -- the first column lands **8 aclk
after its ACT** while tRCD is 3. The ~5-cycle excess is the pick pipeline plus
bank-timer registration on the ACT->column path, and under CLOSE page every
access pays it. During that window BOTH classes are empty (`actm0/colm0`), so
there is nothing for the pipeline to carry and the fix above cannot help --
which is exactly why rbl_dyn (more row hits, columns available) gained and
static_close did not.

Ruled out by measurement, so do not re-try these: tRRD (30.77% at 1, 2 AND 4),
tRCD/tRP/tRC (37.5% with all three at minimum), tFAW, CAM depth (NUM_ENTRIES
8 -> 16 gives 30.77 -> 32.43), the bank guards (a dead cycle measured `grd0`),
and bank recovery (`w_ap_fire` gives a ~9-cycle bank cycle, non-binding
against the 0.5 access/cycle command-bus cap).

### 2026-09-22: residual ACCEPTED -- same by-design root as PUMICE-030

The remaining lever was always "shorten the ACT->column path, i.e. the pick
pipeline depth or the bank-timer registration stage". **Sean 2026-09-22 ruled
exactly that out of scope for [[PUMICE-030]]: "this is by design, many features
need flop stages."** The close-page residual is those same flop stages seen
from the column side, so it is accepted on the same grounds and is NOT a defect.

The outstanding dial -- the lever that IS endorsed for 030 -- was tested and
does not reach it. Board, row_major BL8, 4000 txn:

| config | OS=8 | OS=16 | OS=32 |
|---|---|---|---|
| static_close | 33.9 | 33.9 | 33.9 MB/s |
| open_page | 568.2 | 568.2 | 568.2 MB/s |

Flat to the cycle across a 4x change in transactions in flight, where open_page
is equally flat because it is already saturated. Close page is not
latency-bound and not outstanding-bound: every access pays ACT + column on a
one-command-per-cycle bus, and the ACT->column path is 8 aclk against a tRCD
of 3. More in flight cannot hide a per-access cost.

**So: do not re-open this to chase the 63%.** What remains legitimately open is
only that the paging tests should report the accepted number instead of failing
on it -- a floor that still catches a REGRESSION below the measured point,
which is the next entry.

---
