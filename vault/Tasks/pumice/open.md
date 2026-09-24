<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

## PUMICE-047 — SCHED_WR_WM.wr_batch_max may clobber the whole register on write
**Status:** open 2026-09-23  **Priority:** P2 — an untrusted knob on a fix that
is otherwise verified

`wr_batch_max[23:16]` was added to SCHED_WR_WM (`16eda8ed7`) and the default
path works: the bounded drain is live at reset 16 and the concurrent_rw repro
passes through it. What is NOT proven is the knob.

Writing the field via `tb.csr_write_field("SCHED_WR_WM","wr_batch_max",0)`
behaved as if it wrote the WHOLE register: `wr_batch_max=0` should leave
batching enabled but unbounded (reproducing the starvation), and instead the
cell PASSED in 43s — the signature of batching being disabled outright, i.e.
`wr_high_wm` going to 0 as collateral. The same edit broke 4 `gen_replica`
cells, consistent with one cause.

The readback assert did not catch it because it reads the same field it wrote.

**Do:** check `csr_write_field`'s read-modify-write against a multi-field
register, then re-run the mutation — `wr_batch_max=0` MUST fail the repro
(~347s timeout) or the knob is decorative. Until then do not tune this field on
silicon.

**2026-09-23 — STRONG CANDIDATE ROOT CAUSE FOUND, and it is not
`csr_write_field`.** Found while regenerating registers for [[PUMICE-013]]:
`dv/tbclasses/pumice_regmap.py` is a SECOND generated copy of the pumice
regmap, and it had never been regenerated after `16eda8ed7` added the field.
It is the map the component TBs load (`pumice_top_csr_tb.py:132`,
`pumice_top_tb.py:57`), and in the stale copy:

- `wr_batch_max` **did not exist at all**;
- `RSVD` spanned **31:16**, i.e. straight across the new field's bits;
- the register default read `0x00000102` instead of `0x00100102`.

Any read-modify-write seeded from that map therefore writes ZEROS over
`[23:16]`, which is exactly the "wrote the whole register" signature the task
describes — no defect in `csr_write_field` required. The stale copy is
regenerated and both in-tree maps now agree (`wr_batch_max` present,
`RSVD` 31:24, default `0x00100102`).

This is a CANDIDATE, not a closure: the task's own mutation is still the test.
Re-run it against the corrected map — `wr_batch_max=0` must fail the repro at
~347 s. If it now does, this was the cause and 047 closes; if it still passes,
the clobber is real and lives elsewhere.

The wider lesson is the duplicate: two generated copies of one regmap, only one
of which the `-o` in the regen command targets, is precisely the orphan-drift
trap in [[feedback_peakrdl_generate_bin]]. The second copy silently served a
month-old register layout to every component test.

---

## PUMICE-048 — the +25-30% batching gain was measured with the broken drain
**Status:** open 2026-09-23  **Priority:** P2 — a published number that is
currently unsafe

[[PUMICE-039]] records write batching recovering **+30.3% at gap 12 (240.7 ->
313.7 MB/s)** and +25.7% at gap 15. Both were measured on silicon with the
UNBOUNDED drain — the configuration since shown to starve reads
([[PUMICE-039]], fixed `fc83c1b3c`). The gain is therefore not attributable: it
was taken from a controller that was not servicing reads correctly.

The bounded drain should keep nearly all of it — tRTW amortises across the
batch, so 20 cycles over 16 writes is 1.25 each against 20 for a single
direction switch — but that is an argument, not a measurement.

**Do:** rebuild the bitstream with `fc83c1b3c`+, reprogram, re-run
`run_smoke.py --sequences init wr_batch`, and restate or retract the figure in
PUMICE-039. Needs the board.

---

## PUMICE-046 — close-page modes reach only ~63% of their own command-bus ceiling
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

## PUMICE-034 — the paging predictors are built unconditionally and the board never uses them
**Status:** open 2026-09-14  **Priority:** P2 — pure headroom, no correctness impact

`u_page_policy` (the mode 5 row predictor plus the mode 6/7 RBL table) is
**4,546 LUT / 3,341 FF**, a third of pumice's LUTs, instantiated with no build
gate. The board's default runs use `open_page` and never select modes 5/6/7, so
that area is carried and never exercised on a part where it is the difference
between comfortable and tight.

It is also where timing dies first when anything else grows: across the
2026-09-13 builds `u_row_pred` owned 340-920 of the failing endpoints every
time, more than any other block.

**The tension, which is why this is not simply a fix.** The modes were restored
specifically so that ONE bitstream characterizes every policy
([[project_pumice_advanced_sched_modes]]). Gating them trades that away for
area. Both positions are defensible and it is Sean's call, not a session's.

**Options, in increasing order of how much they give up:**
1. A `PAGE_PRED_MODES` parameter defaulting ON, with the board build turning it
   off. One bitstream per policy family instead of one for all.
2. Gate only the RBL table (248 LUT / 1,488 FF) and keep the row predictor.
3. Leave it and accept the area; revisit if a build stops closing.

**Context for the decision:** the four-generator build closes at **+0.016 ns**
with **87.1% slice occupancy**. There is not much room left for anything else to
grow, and this is the largest single block that is optional.

---

## PUMICE-035 — no stall-cause attribution, so the overhead breakdown cannot be published
**Status:** open 2026-09-14  **Priority:** P2 — blocks a documented reporting gap

The bus meters classify every cycle into productive / backpressure / starvation
/ idle. That says the controller did not accept a beat; it does not say **why**.
So the natural and most useful line of a characterization report -- the missing
percent split into refresh, activate/precharge, bus turnaround and
first-transaction latency -- cannot be produced from anything the design
currently exposes.

`docs/DDR2_BANDWIDTH_MEASUREMENT.md` §5 states this explicitly and leaves the
table out rather than printing a plausible split. That is the right call for
now and a poor permanent answer: every reader of a bandwidth number wants to
know where the rest went.

**What would close it:** a small set of counters in the scheduler attributing
each stalled cycle to the timing constraint that caused it -- tRCD, tRP, tRFC,
tWTR/tRTW, or "no command ready". Four or five counters and a CSR window. The
existing meters already prove the window discipline works; this is the same
pattern one level deeper.

**Why it is P2 and not P1:** the direction is already recoverable from the
buckets we have (backpressure means DRAM-bound, starvation means
requester-bound), which is enough to choose what to fix. The attribution makes
the report complete, not the debugging possible.

---

## PUMICE-030 — read latency is ~2x LiteDRAM's, and it caps small-burst reads
**Status:** DEFERRED FAR 2026-09-22  **Priority:** P3 — BY DESIGN, not a defect

**Sean 2026-09-22: "030 is this way by design, many features need flop stages,
so defer 030 far into the future."** The latency is the price of the pipeline
those features live in, and it is accepted. Do NOT re-raise it as "the largest
identified defect left", do NOT re-measure it to make the case again, and do
NOT trade pipeline depth for it without being asked. The measurements below
stay because they are correct and because they size what the choice costs --
they are documentation of a trade, not an open bug.

The consequence worth REMEMBERING rather than fixing: small-burst read
bandwidth is `outstanding / latency` and nothing else, so the lever that is
still legitimately available is the OUTSTANDING dial (ceiling 32, and the
board proves it -- AxLEN 2 and 4 both reach ~94.5% at 32 outstanding where
they sit at 35%/68% at 8). Reach for that, not for the pipeline.

(Historical framing below, from when this was believed to be a defect.)

**The bug: ~49 MC cycles of read latency against LiteDRAM's 24.7** on the same
board, the same PHY and the same harness. Roughly 24 cycles of extra pipeline
for the same DRAM access. Neither 2026-09-10 bandwidth fix (the intake admit
stage, the return-ring depth) moved it.

**Why it matters beyond latency: it caps small-burst read BANDWIDTH.** Reads at
AxLEN 1/2/4 reach 16%/31%/60% of peak while writes hold 95% on the same
addresses. This was previously written off as "per-transaction overhead, a
mechanism nobody has identified". It is identified: **Little's law**, against
the read generator's 8-outstanding-burst budget.

Model: `min(8 x AxLEN / (read_latency + AxLEN), 0.95) x 8 B x 75 MHz`

| AxLEN | predicted MB/s | measured 2026-09-10 | measured 2026-09-14 | rd latency |
|---|---|---|---|---|
| 1 | 90.7 | 96.2 | 98.3 | 51.9 |
| 2 | 192.0 | 188.1 | 196.3 | 48.0 |
| 4 | 351.8 | 359.9 | 368.2 | 50.6 |
| 8 | 570.0 | 570.5 | 570.5 | 50.2 |
| 16 | 570.0 | 570.7 | 570.8 | 96.0 |

Board-measured with `bin/axlen_sweep.py`. The 2026-09-14 column re-takes the
curve on the rewritten harness (bridges removed, 4+4 generators, new data
function) at the same 8 outstanding: the fit survives, so the model is not an
artifact of the old measurement path. `axlen_sweep.py` had to be repaired
first — it was missing `import sys` and had never been runnable since its
original commit f02a4b569.

**DIRECT confirmation, 2026-09-14: the outstanding sweep.** The table above is
still an inference from a bandwidth curve. `bin/outstanding_sweep.py` tests the
claim head-on — if the shortfall is Little's law, the knee must sit near
`latency/AxLEN` and must move as `1/AxLEN`:

| AxLEN | model knee | measured knee | ratio |
|---|---|---|---|
| 1 | 47.7 | none inside 32 (390.6 MB/s at 32, still climbing) | — |
| 2 | 24.1 | 24 | 0.99x |
| 4 | 12.7 | 12 | 0.95x |
| 8 | 6.9 | 8 | 1.17x |

Every model knee at AxLEN 1 and 2 sits at or above the harness's own 32-deep
ceiling, which is why this could not be measured before the runtime dial
existed. The bandwidth values themselves fit the model to 0-6.5%.

**The model is exact, and an earlier version of this task said otherwise.** On
2026-09-14 this table reported the knees at 32 / 24 / 12 and called the 1.3-2x
gap to the model an open anomaly. That was a defect in the SWEEP's knee
detector, not in the controller: it fired on "this point did not gain 3% over
the previous one", which names the first point AFTER saturation, one sweep step
late every time. Scored as "the first N that reaches 95% of the plateau" the
knees land at 0.99x, 0.95x and 1.17x, and the 1.17x is only the sweep grid —
the model wants 6.9 and the available steps are 4 and 8. Fixed in
`bin/outstanding_sweep.py` and re-measured on the board; both the 1/AxLEN
scaling and the constant hold.

The per-point fit is just as good. At AxLEN 4 the model tracks every one of the
eight points from -0.1% to +4.4%, and measured bandwidth sits slightly ABOVE
the prediction throughout, which says the effective latency is marginally
better than the sampled average rather than worse.

**The decisive result: the shortfall RECOVERS COMPLETELY when the budget is
raised.** This is the claim's strongest test — if small-burst reads were losing
bandwidth to per-transaction overhead, more outstanding transactions would not
buy it back. They do:

| AxLEN | at 8 outstanding | best reached | at |
|---|---|---|---|
| 1 | 98.7 MB/s (16.4%) | 390.6 MB/s (65.1%) | 32, still climbing |
| 2 | 196.6 MB/s (32.8%) | **573.1 MB/s (95.5%)** | 24 |
| 4 | 367.9 MB/s (61.3%) | **574.6 MB/s (95.8%)** | 16 |
| 8 | 575.0 MB/s (95.8%) | 575.6 MB/s (95.9%) | 12 |

AxLEN 2 and 4 reach the SAME ~95.8% ceiling as AxLEN 8 once enough reads are in
flight. There is no per-transaction penalty left to explain. AxLEN 1 needs ~49
in flight and the harness ceiling is 32, which is why it alone is still
climbing — not a different mechanism, just a budget that has not reached its
knee.

This also sharpens the fix. The latency is still the defect for a real master
with a shallow budget, but it is now measured that the CONTROLLER can be driven
to 95% at AxLEN 2 — so nothing in pumice's datapath is limiting small bursts.

Durable records: `reports/axlen_sweep.json`, `reports/outstanding_sweep.json`.
Both sweeps only printed until 2026-09-14, which is why the tables above were
previously quoted from scrollback with no artifact to re-derive them from.

**Two things this rules out.** It is NOT a scheduling bug, and specifically it
is NOT "the read cannot be scheduled until the write is consumed on AXI" (a
reasonable guess, checked and discarded): the characterization runs a write
phase to completion and THEN a read phase, so no writes are in flight while the
reads are measured. (That sequencing is also why PUMICE-037 went unseen for so
long: nothing in this area ran both directions at once with a gap until the
2026-09-14 bank/gap sweep.) It is also not the return ring -- the shortfall did not move
between depth 32 and 64.

**Why writes are immune.** pumice returns B at CAM commit, not after a DRAM
round trip, so a write burst retires in a fraction of a read's time and the same
8-burst budget is ample.

**The fix is the latency, and it closes the bandwidth gap with it.** At
LiteDRAM's 24.7 cycles the same 8-burst budget covers AxLEN 4 (8x4/28.7 = 1.11,
i.e. no longer binding) and the shortfall vanishes from AxLEN 4 upward.
Raising `GEN_MAX_OUTSTANDING` in the harness would ALSO move the numbers, but
that is moving the measurement, not fixing the controller -- a real master with
few outstanding reads would still see the latency.

**Where to look.** The read path crosses intake -> rd CAM -> arbiter -> DFI ->
PHY -> aligner -> return ring -> R channel. `ch01_overview/04_pipeline_latency.md`
in the MAS has the per-stage flop counts from the elaborated netlist; compare
that budget against the measured 49 and find the stages LiteDRAM does not have.
The AR-order return ring and the reorder CAM are the obvious suspects, and both
are research features -- this may be a deliberate cost rather than a defect,
but nobody has done the accounting to say which.

---

## PUMICE-029 — pumice is AT REST: what a future session needs to know
**Status:** open 2026-09-10 (informational; do not close, it is the handover)
**Priority:** read before touching pumice

pumice met its targets on 2026-09-10 and was deliberately put down. This block
is the handover, not a work item.

**NEXT ACTION when work resumes: [[PUMICE-030]]** — the ~49-cycle read latency,
about 2x LiteDRAM's on the same board and PHY. It is the largest identified
defect left and it also closes the small-burst read shortfall, so it is one
fix for two symptoms. Everything else on this page is either informational or
a smaller, independent item.

**Where it landed.** Nexys A7, 75 MHz / DDR2-300 / BL4 on x16, peak 600 MB/s:
write 570.3, read 571.3, concurrent read+write 570.1 total (2.00x LiteDRAM
through the identical harness). 14/14 integrity, WNS +0.285 ns on 94 060
endpoints, 219 controller tests plus the 31-test char gate green. Board build:
`PUMICE_SYS_75=1 make bitstream` in `build-perf` (WITHOUT that define you get
66.67 MHz and every number is wrong).

**The three things most likely to waste a future session:**

1. **The sim cannot run the board's geometry** ([[PUMICE-028]]). The core suite
   is BL8 / 64-bit beat / device == beat, so one DRAM burst is FOUR bus beats
   and any per-sub-command rate limit is divided by four before a bandwidth
   assertion sees it. That is precisely how a 2x read throttle shipped green.
   If a board number and a sim number disagree, suspect this FIRST.
2. **Regenerate the bridges on every build, and re-run the gate after.**
   ([[PUMICE-027]], closed 2026-09-11.) The two-writer hazard that stood here
   was fixed entirely by a bridge-generator change -- master-unique fabric IDs
   plus a slave-side CAM keyed on the returning BID -- with no pumice edit at
   all. `ddr2_char_framework/bin/regen_bridges.sh` reproduces the committed RTL
   byte-identically today; if it ever does not, the generated fabric has moved
   under the harness, and the char suite is the thing that will tell you.
3. **The spec collateral dates instantly.** The design/ tables and waves were
   written mid-campaign and asserted a 15%-of-peak controller with five live
   defects long after the board reached 95%. Both halves are now gated
   (`docs/check_kmap_rtl_sync.py`, `design/check_waves.py`) and the generators
   refuse to emit on failure -- but the gates only cover what they cover. Date
   every claim, or re-run it.

**Known-open performance items, none blocking:**
* Read latency ~49 cycles vs LiteDRAM's 24.7 -- now filed as [[PUMICE-030]],
  the largest identified defect left. It also explains the small-burst read
  shortfall (AxLEN 1/2/4 at 16/31/60% of peak): Little's law against the read
  generator's 8-burst budget, five points predicted within 2%.
* The three runtime axes are characterized but NOT tuned -- nobody has picked
  defaults per workload class from the sweep ([[PUMICE-013]]).
* Area: pumice_top is 12 224 LUT / 7 878 FF, ~5x LiteDRAM's controller+PHY for
  equal streaming bandwidth. That is the deliberate research-controller trade
  and is now stated at the top of AT-A-GLANCE.md; it is the obvious target if
  anyone ever wants a product part.

**Operational traps that cost real time here:**
* `PUMICE_SYS_75=1` or the build is 66.67 MHz.
* `ddr2_char_macro` did not thread `RD_RET_DEPTH`; board default is now 64 via
  `PUMICE_RD_RET_DEPTH`. Check a parameter is actually PASSED before believing
  the flow sets it.
* `ddr2_char.num_gen` defaulted to 1 while the board carries 2 per direction.
  Call `sync_gen_config()`; never trust a hardcoded count.
* The char-framework sim is the board gate before any pumice RTL commit
  ([[PUMICE-023]]).

Related: [[project_pumice_read_ceiling_fixed]],
[[project_litedram_same_harness_ab]], [[project_pumice_char_suite]].

---

## PUMICE-006 — QoS + advanced scheduling (post-cleanup)
**Status:** MECHANISMS COMPLETE 2026-08-27 — all three axes implemented
(Axis 1 scheduling, Axis 2 paging, Axis 3 refresh), every mode OFF by
default and mutation-proven. Characterization/tuning split to
[[PUMICE-013]]. Holds open only for mechanism gaps 013 reports back.

**GAPS REPORTED BACK BY [[PUMICE-013]] 2026-09-23** (first board campaign;
full tables under "PUMICE-013 RESULTS"):

1. **P1 -- FIXED 2026-09-23. `PAGE_RBL_CFG.reset_interval` shipped as
   0 = "never", which made modes 6/7 unusable on streaming traffic.**

   **Mechanism (read from the RTL, not inferred from the sweep).** The epoch
   tick is the ONLY writer of `r_cnt <= '0` in `pumice_rbl_table.sv`, and the
   miss counters saturate UPWARD on every tag hit. Tags deliberately survive
   an epoch so a row stays resident. With no epoch there is therefore no decay
   path at all, and the predictor becomes a ONE-WAY RATCHET: once a row's
   counter passes `miss_thresh` the row latches closed, the next access re-ACTs
   that same resident row, that ACT is now a tag HIT so the counter climbs
   further, and the row can never reopen. A single refresh-driven close is
   enough to seed it; streaming then catches every row in turn. This is why a
   sweep of the epoch looked like "0 is bad" -- the epoch was not tuning the
   predictor, it was supplying the only escape from a self-reinforcing loop.

   **Fix:** RDL reset default `16'h0` -> `16'd256` (generated RTL reset
   `16'h0` -> `16'h100`), the RTL header comment corrected to say a nonzero
   epoch is required by BOTH modes rather than just mode 7, and the host's
   `CONFIGS["rbl_static"]` no longer pins 0 -- "static" there means mode 6's
   static THRESHOLD, not the absence of epochs. 256 is the longest epoch
   measured at full streaming bandwidth (16/64/256 clean, 1024 already
   degrades to 207 MB/s as decay stops outpacing saturation).

   **Verified on silicon after the fix:** `rbl_static` on incremental now
   measures **554.1 MB/s** against 34.9 before -- identical to plain open page
   -- with col_major unchanged at 163.8. Gates: pumice component 188 passed at
   BOTH geometries; char-framework board gate green.

   Original finding below.

   **P1 (as filed) -- `PAGE_RBL_CFG.reset_interval` ships as 0 = "never", and
   that default makes mode 6 unusable on streaming traffic.** RTL reset default is
   `16'h0` (pumice_csr.rdl:716). With the miss counters never decaying, the RBL
   predictor latches closed on streaming and cannot relearn: 34.9 MB/s vs
   553.8 for any nonzero epoch, a **15.8x regression**, with a 0.0% row-hit
   rate and 8.17 ACT/txn -- byte-for-byte close-page behaviour. Isolated by
   sweeping ONLY that field (`bin/seq_rbl_epoch.py`, reproduced twice):
   epoch 0 -> 34.9; epoch 1/16/64/256 -> 553.4-553.8; epoch 1024 -> 207.2.
   col_major measures 163.8 MB/s at EVERY epoch -- it genuinely misses, so the
   predictor is right to close there, which is why this is invisible to a
   page-hostile-only sweep. **Recommend a nonzero reset default in [16, 256].**
2. **P2 -- a windowed or clearable refresh counter.** `REF_STATS_REF`
   free-runs on tREFI, so a host-bracketed delta times the host's UART round
   trips rather than the workload: a 186 us window measured a raw delta of
   61446 (479 ms implied, **2584x**). Worked around host-side in 71c4fb030
   (report window_cycles/tREFI and flag contamination), but axis 3 is
   estimated rather than measured until the counter can be scoped to a window.
   The command counters do not have this problem -- nothing issues DRAM
   commands while the host is idle.
3. **P3 -- config-table confounds, host-side but they distort the axes.**
   `CONFIGS["inorder"]` pairs order_mode=1 with CLOSE page, so the order axis
   reads as a 16x deficit when in-order actually costs 3.9x at equal page
   policy; and all four axis-3 refresh configs pin CLOSE page, measuring
   refresh in the ~34 MB/s regime where it matters least.

**Progress:**
- Step 1 (e64c824b): full mode-select CSR surface + *_STATS telemetry
  registers, defaults bit-identical.
- Axis 2 partial: `pumice_page_policy` fub — modes 1/2 (static ap override),
  3 `fixed_open` (per-bank idle-timeout close via a new lowest-priority
  arbiter PRE branch, JEDEC-gated like the conflict-PRE path) and
  4 `adapt_time` (Happy adaptive-timeout TR/MC walk) + the always-on page
  hit/miss/empty + ACT/PRE/REF counters feeding the *_STATS CSRs.
  Directed test `test_pumice_core_fixed_open` is self-checking both ways
  (mode-0 inertness arms) and mutation-proven (w_timeout_on=0 → RED).
- Axis 2, modes 6/7 `rbl_static`/`rbl_dyn` landed: new `pumice_rbl_table` fub
  (per-set-associative row miss-counter table, tag=row, true-LRU, runtime
  ways/sets shape from PAGE_RBL_CFG, epoch counter clears, mode-7 divider-free
  hill-climb on hit fraction with direction memory). Verdict latched per bank
  at ACT time → page_policy turns the mask into per-bank auto-precharge.
  Directed `test_pumice_core_rbl`: arm A mode-0 thrash baseline, arm B
  thresh=2 static (conflict-PRE suppression < half of baseline + friendly-row
  zero-reACT check), arm C dyn smoke + disarm. Mutation-proven (verdict
  forced 0 → arm B RED: 13 vs 11 PREs, no suppression). Gate tier after:
  fub 40 / macro 3 / top 57.
- Axis 2, mode 5 `adapt_access` landed — AXIS 2 COMPLETE. New
  `pumice_row_pred_table` fub (Happy "Hybrid"): tagless direct-mapped 2-bit
  saturating counters, {bank, XOR-folded row} index; explicit-PRE closes teach
  from accesses-per-activation (<=1 -> close-friendly, >=2 -> open-friendly),
  auto-precharge closes are judged by same-row premature reopen (decrement).
  PAGE_POLICY_CFG.ctr_open_max/ctr_init wired (0 = defaults 2 / weak-open 1;
  init applies while the mode is disabled). LESSON captured in the RTL
  comment: the scheduler's exported row-active bit clears at PICK time, a
  cycle before the PRE issues — the first cut guarded PRE-learning on
  row-active and learned NOTHING (found via $display trace, "PRE bank=4
  act=0"); the open-row IMAGE stays valid, the active bit does not.
  Directed `test_pumice_core_acc` (single-access thrash — a write+read pair
  is 2 accesses and correctly teaches OPEN, so the rbl thrash pattern does
  not transfer): mode-0 baseline, mode-5 suppression < half, golden readback,
  friendly-row zero-reACT, ctr_init=3 cold-table <=1 PRE, disarm. Mutation-
  proven (verdict forced 0 → arm B RED: 12 vs 11 PREs).
  MAS 08_page_policy / design-requirements / HAS open-issue 5 updated to the
  as-built modes 5/6/7.
- Axis 3 step 1: REF_CTRL postpone/pullin JEDEC +-8 credits landed
  (refresh_ctrl v3). Backlog + pull-in credit as one next-state evaluation;
  postpone clamped to 7 so the saturating-8 backlog always forces under
  demand; pull-in runs ahead only on CONFIRMED idle (16-cycle hysteresis
  over scheduler CAM occupancy — micro-gaps must not release postponed
  refreshes). TWO integration traps found and fixed in the same change:
  (1) drain_active gated on refresh_req_o, else the arbiter's drain
  preemption defeats postponement entirely; (2) the tREFI counter reloads
  only on expiry, so a runtime t_refi poke takes effect after the STALE
  period elapses once (test waits it out — this also bit the first test
  run as a false "refresh gated" red).
  Directed test_pumice_core_refresh_credit (timed demand windows, not
  write counts — 40 b2b writes span <2 ticks): strict red-guard, postpone
  zero-leak + forced ceiling + drain conservation, pull-in run-ahead +
  refresh-free demand window + golden readback, disarm. DOUBLE
  mutation-proven: postpone gutted -> arm B RED (6 leaked); pull-in
  gutted -> arm C RED (tick-rate only).
- Axis 3 step 2: refpb_rr landed (REF_CTRL.mode=2, LPDDR2-only with DDR2
  degrade + perbank_supported strap). RDS-DV model first (041ddc3):
  dram_state.on_refresh_bank with device-internal rotor, per-bank tRFCpb
  recovery, bank-aware cmd_during_refresh (other banks accessible), 6 unit
  tests; slave routes decoded all_banks=False to it. RTL: arbiter 2b branch
  (PRE rotor bank only -> OP_REFPB; rank-wide-ACT-block-during-tRFCpb
  conservative v1), refresh_ctrl tREFIpb mux + rotor mirror.
  TWO REAL BUGS found by the directed test's zero-data reads:
  (1) LATENT DOUBLE-ISSUE: every refresh fired TWICE (grant->req-drop is
  2 cycles; the 2nd command registers before rfc_busy loads). Benign-
  looking for REFab (a silent tRFC-between-REFs violation, present in
  every prior build INCLUDING board bitstreams) but fatal for REFpb —
  each command advances the device rotor -> mirror desync -> wrong-bank
  precharges -> rows silently closed -> no_act_before_rd zero reads.
  Fix: !r_grant in w_ref_safe/w_refpb_safe.
  (2) rotor-mirror sampling: grant fires at the arbiter's FIFO-PUSH, so
  grant_was_pb must sample the ARBITER-side a_cmd_op, not cmd_op_o (the
  FIFO HEAD = an older command; sampling it stalled the mirror).
  LESSON: the fub arbiter test's refresh poll (2-edge settle stride) had
  been passing BECAUSE of the double-issue — the bug kept REF visible for
  two cycles and the sampler always caught the second one. Single-issue
  made the 1-cycle REF invisible to the stride; the poll now samples
  every edge. A test that samples slower than the event it checks can be
  green only in the presence of the bug it should catch. (The SAME
  stride bit AGAIN in the Axis-1 fub arm: with static vectors the picks
  alternate RD/ACT at period 2 and settle()'s 2-edge stride phase-locked
  onto the non-RD cycle — hours chasing phantom "livelocks" before the
  mask probe showed the RD firing all along. Order-mode polls are now
  per-edge too.)
  Directed test_pumice_top_refpb (LPDDR2 top TB): strap check, REFab
  red-guard (refpb_total==0), full rotation >=8, BFM traffic golden
  THROUGH the refpb stream, zero refresh-class model violations, disarm.
  Mutation-proven: mode gate gutted -> arm B RED (0 REFpb).
  AXIS 3 REMAINING: none in the commodity plan (per-bank ref_credit
  steering + ACT-during-tRFCpb overlap are cataloged optimizations).
  ALSO NOTE: the editable RDS-DV install was silently replaced by the
  0.6.5 wheel at the release pin-bump — [[reference_dv_framework_repos]]
  has the recovery (rm the site-packages copy, pip install -e, verify
  __file__).
- Axis 1 step 1: ORDER_MODE landed (SCHED_POLICY.order_mode 1=in_order /
  3=age_threshold + age_thresh; 0/2 = FR-FCFS default). CAMs export a
  per-entry 1-bit aged flag + head relative age (numeric ages never leave
  the CAM); the arbiter overlay only NARROWS the FR-FCFS class masks.
  A REAL PRE-EXISTING BUG found by the directed test's parked-victim
  pattern (same-bank conflict read held while row-hits stream): a
  conflict-PRE fires in a column-readiness gap, then a COLUMN picks
  against the 2-cycle-stale row-open image and lands on the closed row —
  its data never returns and the rd reorder CAM's AR-order drain WEDGES
  forever (rd-return checker DROP). Reproduced on pristine HEAD RTL
  (bisect harness), latent since the bank-parallel refactor. Fix =
  PRE-only THREE-cycle column guard (w_pre_col_guard; PRE-only because
  the general w_guarded also covers RD/WR fires and would throttle
  same-bank column streaming — the first broad fix broke the fub
  CLOSE->WRA arm; three deep because the bank image is up to 3 cycles
  stale end-to-end and the 2-deep version still wedged).
  A SECOND pre-existing bug behind the residual deterministic wedge: the
  DFI READ-RETURN PATH SILENTLY DROPPED BEATS — dfi_rddata_valid is
  fire-and-forget (no PHY backpressure) and the rd aligner forwarded
  beats into the return CDC FIFO with ready gating only its capture
  counter; a beat arriving while the 16-deep FIFO was full was simply
  gone (probe: 4 beats lost), the burst went short, and the AR-order
  drain wedged behind it. Fix = RD_FIFO_DEPTH 16 -> 32 (sizing contract:
  the return FIFO must cover the whole admission domain = rd-CAM depth x
  BL_WORDS = 32 beats) + a HARD ASSERTION in the aligner so any future
  valid-with-full cycle is an $error, never silent data loss.
  TWO design lessons: (a) the rd reorder CAM releases AXI reads in AR
  order BY DESIGN, so completion order at the core level can NEVER show
  scheduling differences — order-mode semantics are verified at the FUB
  arbiter level (hand-driven vectors, scenario 11), the core test is the
  wedge/integrity sentinel across modes; (b) age_threshold's boost must
  trigger on the aged entry's EXISTENCE, not its candidacy — a
  guard-blocked PRE never becomes a candidate while the competing column
  keeps firing and re-arming that same guard (self-sustaining starvation
  of the anti-starvation mechanism). Mutation-proven (overlay gutted ->
  in_order arm RED).
- Axis 1 step 2: ROW_SEL/COL_SEL most/fewest_pending landed
  (SCHED_POLICY.row_sel/col_sel). Per-entry pending population = 8x8
  same-{bank,row} match triangle per CAM (the paper's "expensive
  counters" are trivial at CAM depth 8); arg_sel picks population-first
  with OLDEST tie-break, composing under the ORDER_MODE narrowing;
  row_sel steers ACT, col_sel steers COLUMN, PREs stay oldest. Fub
  scenario 12 (hot-row-vs-lone-old vectors, per-edge polls) proves all
  three encodings both directions; mutation (selector forced to oldest)
  -> RED by drain-loop timeout. Core sentinel sweep extended with
  most/most + fewest/fewest arms.
- Axis 1 step 3: ACCESS_PREF landed (SCHED_POLICY.access_pref: 0/1
  column_first = legacy order bit-identical, 2 row_first, 3
  precharge_first). Class chosen first from the (ORDER_MODE-narrowed)
  per-class picks, read-over-write within. TESTING LESSON: the first fub
  scenario (poll-for-op over static self-refilling vectors) PASSED ITS
  OWN MUTATION -- fired picks arm guards, the preferred class blanks a
  cycle, and every class appears in the alternation, so any op is
  findable under any preference. Rewritten as ONE-SHOT candidates with
  FIRE-ORDER asserts (deterministic total order per preference) + a
  4-cycle inter-arm pipeline flush (registered picks straddle arm
  boundaries and get booked to the wrong arm). Mutation now properly
  RED (pref dead -> column-first order under the row_first arm).
- Axis 1 step 4: write batching landed (SCHED_WR_WM.wr_high_wm/wr_low_wm
  hysteresis on wr-CAM schedulable occupancy; while draining, writes
  outrank reads in every class; 0 = disabled bit-identical). Fub
  scenario 14 (fire-order: wm off -> RD first; 3/1 -> two WRs front-run
  the read), mutation-proven (drain forced off -> RD-first RED).
- Axis 1 step 5: prio_sub landed (SCHED_POLICY.prio_sub: 0/2
  load_over_store default bit-identical, 1 none = per-fire direction
  toggle, 3 age_boost = an aged write winner pierces read priority via
  the age_thresh flags). Per-class write-first decision with precedence
  drain > prio_sub. Fub scenario 15 (fire order: default RD-first,
  none = both fire, age_boost aged-WR-first + unaged RD-first),
  mutation-proven (decode dead -> age_boost arm RED).
- Axis 1 step 6: QoS landed (SCHED_POLICY.qos_en) — AXIS 1 COMPLETE.
  AxQOS now carried AR/AW -> intake -> CAM entry -> per-entry sch_qos
  vector (it previously died at the burst chopper); with qos_en each
  class narrows to its max-QoS candidates BEFORE the population/oldest
  select, making QoS the outer key with the existing selects as the
  inner tie-break. Fub scenario 16: qos_en=0 picks the oldest (slot 5),
  qos_en=1 picks the OLDEST OF THE MAX-QOS SET (slot 6, not the younger
  slot 7) — proving both the outer key and the surviving age tie-break.
  Mutation-proven (narrowing dead -> picks slot 5, RED).
  ALL of PUMICE-006's three axes are now implemented: Axis 1
  (scheduling), Axis 2 (paging), Axis 3 (refresh).
  **MECHANISM WORK COMPLETE 2026-08-27.** Characterization and tuning of
  the landed modes is a large body of work in its own right and moved to
  [[PUMICE-013]] (Sean, 2026-08-27). 006 now covers only the RTL
  mechanisms + their directed/mutation-proven mode tests; it closes when
  013 has no mechanism gaps to report back.
- Direction (Sean, 2026-08-25): RETIRE the legacy HAPPY_HYBRID predictor —
  the new Happy-derived modes are its successors; docs to describe the
  actual implementation.

The original framing ("once pumice is CLEAN, layer in the sophisticated
features") is satisfied: the advanced-mode catalog in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md` and the
design-requirements doc (FR-FCFS variants, paging/refresh policy modes, QoS)
is implemented end-to-end, each mode OFF by default with encoding 0 = build
default and every mechanism mutation-proven at the fub level.

**Entry gate (met):** tiny-tREFI soak 0-dirty on the rebuilt bitstream
(PUMICE-004).

---

## PUMICE-013 — characterize + tune the advanced modes (all three axes)
**Status:** open 2026-08-27, FIRST CAMPAIGN LANDED 2026-09-23 — all three axes
swept one-at-a-time on the board, results and recommended defaults in
"PUMICE-013 RESULTS" below. Four mechanism gaps reported to [[PUMICE-006]],
one of them a shipped RTL default that costs 15.8x on streaming. Still open
for the axis PAIRS, the axis-3 re-run under open page, and the scheduler
sub-knobs that were not reached (listed under "What is NOT yet characterized").
(split out of PUMICE-006 at Sean's direction —
"move characterization to its own task as that is a big one")

PUMICE-006 delivered the MECHANISMS: every mode of all three axes is
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
mechanism gaps found reported back to PUMICE-006 before it closes.

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

### PUMICE-013 RESULTS -- board campaign 2026-09-23

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

### Mechanism gaps -> [[PUMICE-006]]

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
refresh), the `SCHED_WR_WM` write-batching interaction (PUMICE-048 has its own
board number to re-measure), `prio_sub` / `qos_en` / `row_sel` / `col_sel`,
and the axis-3 re-run under open page. There is also no genuinely RANDOM family
-- `col_major` is the page-hostile proxy -- so "random" in the workload table
above is not directly measured.


## PUMICE-023 — the char-framework sim is the board gate and must run before any pumice RTL commit
**Status:** open 2026-09-08  **Priority:** P1

`ddr2_char_framework/dv/tests` (test_ddr2_char_uart + test_ddr2_char_char) is
the only suite that builds the board's x16 / strict-timing configuration. The
arbiter fix passed all 213 pumice fub/macro/top tests and failed 7 there
(write side, fixed by the write-staged gate). Its Makefile `run-all-*` targets
were being swallowed by the `run-%` pattern into a nonexistent test id, so the
area had silently stopped gating; aliases added 2026-09-08. Pre-existing
failures to triage: `smoke_rate2_faithful`, `smoke_rate2_rdphase1`,
`smoke_rate2_strict`, `pagehit_rate2_x16_free_earlyen` (all fail at
79fb58a66, before this session). Add this directory to the pumice regression
convention (`regressions` skill) and to the components master Makefile.

## PUMICE-CLEANUP — doc + filelist cleanup (push from workstation)
**Status:** open 2026-07-24 — deferred (project cleanup; see TOOL-010)
**Priority:** P2

Apply the RTL-area cleanup pattern to pumice: doc placement ([[doc-placement]])
and filelist consistency ([[filelists]] — the `dv/tb/*_tb_top.f` move into a
`filelists/` dir co-located with the testbench).

**⚠️ Pushing: Sean pushes pumice from the workstation, NOT from the agent
environment (Sean, 2026-07-24).** Make and commit the pumice changes here if
working, but leave the push to Sean. Do not `git push` pumice work from this
box. (Reason per Sean — workstation is where pumice is pushed from.)

Gated behind the RTL area completing (Tasks/INDEX.md sequencing).

## PUMICE-039 — batch same-direction columns to amortise the R/W turnaround
### 2026-09-23: batching had a READ-STARVATION defect; fixed, and the old validation was geometry-bound

**The "+25-30% recovery, clean" record below was measured with a broken
feature.** SCHED_WR_WM latched the drain at wr_high_wm and cleared it only at
wr_low_wm, so a CONTINUOUS writer held occupancy above low_wm forever, the
drain never released, and READS NEVER ISSUED. It could not self-correct: the
drain overrides prio_sub entirely and SCHED_POLICY.age_thresh is 0 by default,
so sch_age_exceed_o is inert -- there was no anti-starvation path on that
branch at all.

Fixed in `fc83c1b3c` by BOUNDING the batch (WR_BATCH_MAX, now the CSR field
SCHED_WR_WM.wr_batch_max, default 16): after N write columns the drain yields
and r_rd_owed blocks re-arming until a read column actually fires. tRTW
amortises ACROSS the batch, so 20 cycles over 16 writes is 1.25 each and an
unbounded drain buys no further amortisation.

Bisected by DOUBLE TOGGLE, since the range contains the feature switched on,
off and on again: 16119318a ON -> BAD, bc36f2d28 OFF -> GOOD, 1f6a3bfdf ON ->
BAD. Corroborated by bank_gap_sweep going 242 failures -> 0 with
TEST_WR_HIGH_WM=0.

**Why the original validation missed it, which matters more than the bug.**
"210 concurrent runs, 0 failures; 1008 matrix cells, 1 unattributed beat" is
real, and all of it ran BL8 through the char harness. None of it ran bl4x16
through pumice_top, where one AXI beat is one DRAM burst and a single writer
can hold the CAM above the watermark indefinitely. `bc36f2d28` reverted
batching over ONE failing cell and `1f6a3bfdf` (mine) put it back arguing 1008
clean cells outweighed that. The reverter was right with less evidence. This is
[[PUMICE-028]]'s thesis in one incident: a conclusion valid in the geometry the
suite could express, with a hole exactly where it could not.

[[PUMICE-045]] ("one unattributed mismatched beat in 1008 cells") was the
evidence used to justify that re-enable. It should be re-examined now that
batching is known to have starved reads -- the beat may not be unattributed.

**The +25-30% board figure is NOT restated here.** It was measured with the
unbounded drain. Re-measure against the 16-write cap before quoting it.

**Status:** DEFERRED 2026-09-17  **Priority:** P3
**Corruption FIXED and proven (210 clean board runs). Deferred on timing only --
and that timing is ACCEPTED: Sean 2026-09-17, "this is designed for aggressive
timing." Do NOT re-raise the +16 ps margin as a blocker.**

2026-09-16: the mechanism ALREADY EXISTS -- `SCHED_WR_WM` in
pumice_cmd_arbiter.sv, shipped with high_wm=0 (disabled) and, until
6ba9dba62, with no host accessor at all. Enabling it on the board recovers
**+25-30% bus bandwidth** (240.7 -> 312.6 MB/s at gap 12), more than the
-17.4% that PUMICE-037's tRTW=20 costs.

It also CORRUPTS: 4 beats/run, 50% all-ones -- PUMICE-037's DQ-collision
fingerprint. Cause is NOT the arbiter (see PUMICE-042): with CMD_HISTORY_EN
armed, check (7) GLOBAL tRTW fired ZERO violations while batching was on with
the watermark readback verified. The scheduler spaces correctly; the DFI cmd
path compresses it.

### 2026-09-16 (later): batching STALLS. Default reverted to disabled.

The clean-and-fast result below was measured at gaps 12 and 15 ONLY. A wider
sweep (seq_wr_batch, 8 gaps x 2 generator counts x 3 watermarks x 4 reps = 192
runs) found intermittent stalls immediately:

    hi=0 (off)   16 points   0 non-clean
    hi=2/lo=1    16 points   1 -- 1+1 gap=4,  2/4 runs, timeouts=2, [360,0,0,359]
    hi=8/lo=4    16 points   1 -- 1+1 gap=11, 1/4 runs, timeouts=1, [0,0,1,0]

**CORRECTION (same day):** that "matching timeout count" was an artifact of my
own instrument, and the conclusion drawn from it was WRONG. The sequence
counted `not r.ok` as a timeout, but pumice_char computes

    ok = wr_ok and rd_ok and mism == 0 and rd_total == expect_rd_txn

so `not r.ok` counts MISMATCHES too, and "fails == timeouts" was tautological
rather than corroborating -- the two were computed from the same condition.

Re-measured with engine completion read from the NOTES instead: `stalled=False`
on every failure, `timeouts=0` everywhere. **Both engines complete. This is
data corruption, not a stall.**

    hi=0 (off)   0/8 failing
    hi=2/lo=1    2/8 failing   mism = 180, 359
    hi=8/lo=4    1/8 failing   mism = 360

Batching-off is clean on the identical workload. The counts are QUANTIZED
around 180 and 360 (and 179/359, one short) out of 16000 beats per run --
roughly 1.1% and 2.2%, with 360 = 2x180. Random DQ collisions would scatter;
a fixed ~180-beat unit means something structural is mis-delivered. Identifying
what has size 180 (region, CAM depth, drain length, burst count) should name
the mechanism.

PUMICE-042's fix cleaned gaps 12/15 but NOT gap 4.

**Both failures are at 1+1 -- which is also the ONLY configuration batching
helps.** +30.6% at 1+1; ~0% at 2+2/3+3/4+4, where the bus plateaus at ~160 MB/s
regardless because multiple generators already keep same-direction work queued
and there is no turnaround left to amortise. So the one regime it benefits is
the one where it breaks.

**Correction:** the two bank_gap_sweep runs that died/stalled in the 2+2 stage
were blamed on the sweep script, on the strength of a measure_concurrent check
at gap 12 ONLY showing no timeouts. Both had batching defaulted on, and
batching demonstrably stalls at other gaps. Same defect -- the tooling was not
at fault.

**PUMICE-043 folds into this** -- its 1-beat-in-1/8 residue at hi=8 is the same
corruption at a different gap, not a separate defect.

### ILA, 2026-09-17 — the DRAM is not driving; pumice returns that faithfully

Capture on a failing run (trigger rd_dbg_mismatch, batching hi=2/lo=1, gap 4,
1+1), reports/ila_pumice039_batching.csv:

    valid beats 940, mismatched 180
    all-ones (undriven DQ)            91/180
    wrdata_en during a read return     0 cycles
    dfi_rddata == rd_dbg_actual        EVERY mismatched beat

Three things follow, and they redirect the search:

1. **NOT PUMICE-042's mechanism.** Zero write-during-read overlap. The DFI-side
   turnaround fix is not implicated.
2. **pumice does NOT mangle the data.** What the PHY delivers is bit-for-bit
   what the reader receives.
3. **The DRAM is not driving DQ.** The captured beats alternate between
   all-ones (undriven) and ONE repeated stale word (2b53168cedf9d1c9) -- the
   a7ddrphy's free-running ISERDES holding its last captured value. The
   capture window is opening over a bus with nothing on it, for ~180 beats.

Ruled out by measurement:
  * read alignment -- batching is WORSE at the old rden=6/delay=7 (4/12 and
    3/12 failing) than at rden=1/delay=2, so PUMICE-040 is not implicated
  * accumulated state -- per-rep soft_reset (every CSR to RTL default, geometry
    restored) does not change the rate
  * over-delivery -- stray=0 on every failure
  * cell damage -- the post-failure read-only audit is always mism=0
  * engine stalls -- stalled=False, timeouts=0

**Leading hypothesis:** the write drain's ACT/PRE activity closes a row that an
already-issued read depends on, so the read finds no open row and the device
drives nothing. That is the same class the arbiter's w_ap_col_guard /
w_pre_col_guard exist for (issue #42: "batch-2 row-1 writes landed on row 0"),
and a long uninterrupted write run is exactly what would defeat a guard sized
for ping-pong traffic. Testable: CLOSE page policy, or writer/reader forced
onto banks that share no rows.

**CLOSE page is clean -- but the test is CONFOUNDED.** baseline (page_policy=2)
runs 0/12 failing at every watermark, where open_page fails 2-4/12. But CLOSE
page also drops the bus from ~435 MB/s to 33 MB/s -- 13x. A clean result at
one-thirteenth the command rate does not separate "row state was the mechanism"
from "the hazard needs a density CLOSE page cannot reach". Suggestive, not
evidence. A better discriminator holds the rate roughly constant while changing
row reuse -- e.g. open_page with writer and reader forced onto banks that share
no rows.

Next: identify the ~180-beat unit (stable at exactly 180 across both read
alignments), and find a row-state test that is not rate-confounded. It is the strongest clue available -- a
fixed quantum of mis-delivered data, not scattered collisions. Candidates:
the concurrent region size (0x20000 per the notes), the read CAM / return-ring
depth, or the number of bursts in one drain.

### Earlier the same day (superseded by the above)

2026-09-16: PUMICE-042 is fixed, and batching is now CLEAN and FAST:
  gap12 hi=2/lo=1  0 mismatched, bus +29.9%
  gap15 hi=2/lo=1  0 mismatched (0/8 reps), bus +25.0%
hi=2/lo=1 is both the cleanest AND the fastest setting -- higher watermarks
give LESS bandwidth and a residual (PUMICE-043), so there is no trade-off to
tune. What remains is deciding whether to make it the BUILD DEFAULT (currently
high_wm=0 = disabled) and validating that with a batching-ON matrix + gate.

PUMICE-037's fix costs **-17.4% of bus bandwidth at gap 15** (writes -17.4%,
reads unaffected): the arbiter pays the full ~18-cycle tRTW on EVERY direction
switch, and at high gap nearly every read is isolated so nearly every one
charges it. Gaps 0-12 cost nothing.

LiteDRAM does not pay per switch. Its multiplexer stays in READ until reads are
exhausted or an anti-starvation timer fires, then pays its turnaround ONCE for
the whole batch (`multiplexer.py`: `if write_available: if (~read_available |
max_time0)` -> the RTW chain). pumice's flat FR-FCFS arbiter interleaves freely.

pumice's own source already anticipates this -- `pumice_cmd_arbiter.sv:80`:
"write drain amortizes the tWTR/tRTW bus turnaround instead of ...".

Realignment cannot substitute: tRTW is alignment-independent (proven on the
board, PUMICE-037). Batching is the only route that recovers this bandwidth.

### 2026-09-17: ROOT CAUSE FOUND ON THE ILA -- a swallowed ACT inside tRFC

`reports/ila_pumice039_batching.csv` (hi=2/lo=1, gap 4, 1+1, a 180-beat
failure). The 180 bad beats are NOT scattered and NOT corrupt data:

    distinct ACTUAL values on 180 bad beats: 2
        0xffffffffffffffff   x91    undriven DQ (bus pulled high)
        0x2b53168cedf9d1c9   x89    one stale word held by the ISERDES

That is an IDLE DQ BUS. a7ddrphy's free-running ISERDES holds its last capture,
so "all-ones alternating with one fixed word" means the DRAM drove NOTHING and
pumice sampled the float. Confirmed on the DFI side independently:
`dfi_rddata_valid` is asserted for **180 consecutive samples (2028..2207)**
while `w_dfi_rddata` carries only those two values -- one unbroken run, exactly
matching the checker's 180 bad beats (they arrive later in 8-beat groups, +4 per
group, which is just AXI burst pacing).

**Why the DRAM was silent.** One tRFC violation in the capture:

    REF @448   -> ACT bank7 @463    gap=15
    REF @1036  -> ACT bank0 @1051   gap=15
    REF @1632  -> ACT bank2 @1635   gap=3     *** VIOLATION ***
                  ACT bank1 @1636   gap=4     *** VIOLATION ***
    REF @2205  -> ACT bank3 @2220   gap=15
    REF @2792/3378/3963 -> gap=15 each

Six of seven refreshes pace the next ACT at 15. The seventh lets two ACTs out
at 3 and 4 cycles. The DRAM is still refreshing, so it DISCARDS them -- bank 1
never opens. Every following read to bank 1 is a column access to a closed
bank, and DDR2 answers by driving nothing. The idle run starts with the first
read return after that swallowed ACT and ends **two cycles after the NEXT
refresh** (REF @2205), which re-synchronises the DRAM with the controller's
bank image; the legal ACT bank1 @2308 (gap 103) then works.

Everything else on the DFI was RULED OUT by the same capture, so do not re-test
these: `wrdata_en` never overlaps a read return (0 cycles); zero column
commands to a closed bank from sample 444 on (3..443 are the ILA window opening
mid-stream); read columns march monotonically +4 with no row wrap; RD->WR
accounting is exact (940 RD, 940 valid samples, balance never negative, the
constant +18 is pipeline depth); and the return stream is NOT slipped -- a lag
scan is flat at 0.11% for every nonzero lag. RD->WR turnaround is 20/27/29,
so PUMICE-042's tRTW fix is working.

**Mechanism: spacing computed in the arbiter is destroyed downstream.** The
arbiter enforces tRFC correctly -- `w_act_gate_live = !w_rfc_busy && ...` gates
every ACT branch, and `r_rfc_cnt` loads on the fired REF. But
`pumice_dfi_cmd_path.sv` gates only COLUMN commands:

    assign w_gate = ((!w_is_col) || w_col_ok) && ...

ACT/REF/PRE pass through ungated. When the column gate stalls the single
command stream, row commands queued behind it in the CDC FIFO lose their
arbiter-enforced idle cycles and drain back-to-back on release. The capture
shows exactly that shape immediately before the bad refresh: ACT@1585,
RD@1589-1591, a **19-cycle dead gap**, WR@1611, another gap, 14 back-to-back
reads @1615-1628, then PRE/PRE/PRE/REF/ACT/ACT @1629-1636 as one solid
unpaced run. The good refresh @2205 shows the correct shape: four PREs, REF,
then a clean 15-cycle gap before ACT.

This is PUMICE-042's mechanism on a different command pair -- and PUMICE-042's
own fix (tRTW 3 -> 20) LENGTHENED the column stalls, which is why the residue
appeared after it. Write batching triggers it because the drain is what creates
the long column stalls in the first place.

**It is not only tRFC.** Full spacing audit of the DFI stream:

    pair                          n     min   median
    REF->ACT  (tRFC)              7       3       15   one gross violation
    ACT->RD   same bank (tRCD)  754       1      368   2 violations, gap=1
    PRE->REF  (tRP)              40       1        6
    ACT->ACT  any bank (tRRD)    24       1      150   tRRD=1, legal

The two tRCD=1 cases (ACT bank2 @2677 -> RD @2678; ACT bank3 @3336 -> RD @3337)
are the reader's bank-handoff ACTs and did not corrupt in this run -- marginal
rather than gross, but the same class and latent.

**Fix direction:** enforce row-command spacing on the DFI side, the way
PUMICE-042 enforced turnaround -- a pacer in `pumice_dfi_cmd_path.sv` loaded on
a fired REF that blocks ACT for `tRFC`, plus a per-bank ACT->column pacer for
tRCD. The CSRs already exist (`TIMINGS_RFC_REFI.tRFC`). The general statement
is that ANY inter-command timing computed upstream of the CDC FIFO is
unenforced on the wire; the column gate is currently the only thing that is not.

**Not yet directly probed:** the FIFO-bunching mechanism is inferred from the
command shape on the wire, not from an occupancy probe. An ILA on the CDC FIFO
level + the arbiter-side command stream would confirm it and is the cheapest
next measurement.

### 2026-09-17: FIX -- the DFI layer no longer holds any timing

Sean: "The dfi layer should be super simple. All delays must come from the
scheduler." That is the correct architecture and it dissolves this bug class
rather than patching one more command pair.

Removed from `pumice_dfi_cmd_path.sv`: the `COL_BURST_CYC` parameter, the
`t_rtw_i`/`t_wtr_i` ports, and the `r_col_pace` / `r_turn_pace` /
`r_last_col_was_rd` / `r_col_seen` pacer. The accept gate is now

    assign w_gate = (!w_is_rd || rd_op_ready_i) && (!w_is_wr || wr_op_ready_i);

-- no timing term, only the two STRUCTURAL holds (aligner slot free, write data
staged), both sized never to fire. `pumice_dfi_layer.sv` and `pumice_core.sv`
drop the duplicate CSR plumbing, so tRTW/tWTR now reach exactly one consumer.

Why it is safe, in order of strength:

 1. MEASURED. This task already records that with `CMD_HISTORY_EN` armed the
    global tRTW check fired ZERO violations while batching was on. The
    scheduler's turnaround enforcement was verified correct under the very
    workload that corrupted -- the arbiter was always right, only the wire was
    wrong. The backstop being removed was never load-bearing.
 2. The tCCD clamp `w_t_ccd_eff = max(t_ccd_i, BURST_WORDS)` has an IDENTICAL
    floor to the deleted column pacer (`BL_WORDS == BURST_WORDS`), so that
    pacer could never fire on a correctly-clamped tCCD. It only ever fired on
    the turnaround -- the 20-cycle stall that compressed everything behind it.
 3. No staleness hole in the arbiter: `trtw_ok_i` is a strict flop of a counter
    that loads a cycle after the RD event, so it is stale for exactly 2 cycles;
    `w_wr_turn_block = r_rdfire0 || r_rdfire1` blocks writes for exactly those
    2 cycles. Continuous coverage, and symmetric for reads.

The path is now constant-latency end to end, which is the property that was
missing: arbiter (all timing) -> CMD_DELAY shift register (fixed N, verified a
token shift reg, not a stall) -> CDC FIFO (cannot accumulate, nothing
downstream stalls) -> DFI cmd path (never inserts a cycle) -> wire. Spacing at
the DRAM pins now equals what the scheduler computed.

Consequence recorded in both files: `w_t_ccd_eff` and the arbiter's forward-tCCD
counter are now LOAD-BEARING -- they are the only things keeping the column
period honest, since nothing downstream will absorb a too-tight tCCD any more.

**Gate:** char-framework `families_x16` PASSES on the final RTL --
sim_time_ns=10,496,600 (10.5 ms simulated, 231.8 s wall), not a vacuous fast
pass. Lint elaborates with no new warnings. Net -64 lines; the DFI command path
loses 98 lines of logic.

**STILL OPEN -- do not close this task.** The sim gate only proves the existing
path is not broken. It does NOT prove PUMICE-039 is fixed, because the failure
is a silicon-only intermittent. Board validation required:
  - bitstream + `seq_wr_batch` with batching enabled at 1+1 gap 4,
  - REF -> ACT must hold at 15 (it was 3), no 180-beat idle-bus runs,
  - and watch for PUMICE-042's RD->WR collision returning, which is the one
    thing this change could regress.

**Follow-up (highest value):** `pumice_cmd_history_checker` watches the ARBITER
OUTPUT, which is exactly why its tRFC check stayed silent through this entire
failure while the wire was violating tRFC by 12 cycles. Retarget it at the DFI
wire and this class of bug is caught in sim instead of by an ILA capture.

### 2026-09-17 BOARD: the DFI fix WORKED for tRFC and exposed a real arbiter bug

Measured on silicon, ILA-verified, 3 watermarks x 10 reps, gap 4, 1+1.

**Round 1 -- DFI pacer removed (5f043e6f8) alone:**

    hi=0 (off)   0/10 clean       <- control, platform sound
    hi=2/lo=1    10/10 failing    ~150 beats
    hi=8/lo=4    10/10 failing    ~155 beats

WORSE than the 2/8 it replaced. But the ILA showed the fix did exactly what it
was designed to do, and named the reason for the regression:

    (1) REF->ACT   min=15  required>=15  violations=0   <- tRFC FIXED
    (2) rddata_valid on an idle bus: all-ones=0         <- 180-beat runs GONE
    (4) RD->WR     min=1   required>=20                 <- NEW: tRTW violated

So the tRFC diagnosis and remedy were both correct. Removing the wire-level
pacer exposed a PRE-EXISTING arbiter defect the pacer had been masking.

**The arbiter defect.** Not FIFO compression -- the ILA shows a lone write
spliced into a back-to-back read stream, surrounding idle gaps regular:

    @2025 RD b0   @2026 RD b0   @2027 RD b0   @2028 WR b2   @2029 RD b0

The column MASKS apply `trtw_ok_i`/`twtr_ok_i` and the fire-history guards at
CLASSIFY time, ~3 pick-pipeline cycles before the command issues. A write
selected while no read had recently fired issues INTO a read burst that started
meanwhile; `w_wr_turn_block` is only 2 cycles wide and is long spent. Four
violations in one 4096-sample capture, all the same shape.

**Fix:** live turnaround re-validation at the FINAL PICK, exactly mirroring the
`w_act_gate_live` pattern already used for ACT (which exists for the identical
staleness reason -- see PUMICE-018).

    assign w_rd_turn_live = twtr_ok_i && !w_rd_turn_block;   // RD after a WR
    assign w_wr_turn_live = trtw_ok_i && !w_wr_turn_block;   // WR after a RD

applied to both column branches, plus the read-priority override so an ILLEGAL
write can no longer defer a legal read. Coverage is continuous at the issue
cycle: cycles 1-2 by the fire history, 3+ by the loaded tRTW counter.

**Round 2 -- with the arbiter fix:**

    hi=0 (off)   0/10 clean    400.6 MB/s
    hi=2/lo=1    2/10 failing  448.2 MB/s   mism [0,1,0,2,0,0,0,0,0,0]
    hi=8/lo=4    2/10 failing  448.2 MB/s   mism [0,0,0,1,0,0,2,0,0,0]

Bulk corruption GONE: magnitude 150-360 beats -> **1-2 beats**, ~100x. Rate back
to the pre-existing ~2/10. Batching now yields +11.9% bus.

**STILL OPEN.** Three things, none of them the bug above:

 1. **1-2 beat residue at 2/10.** Matches the PUMICE-043 signature already
    recorded here (1 beat in 1/8 at hi=8/lo=4), which PREDATES this work. Not
    yet characterised on the ILA.
 2. **Read eye is NARROW and leveling's final verify FAILS, reproducibly.**
    `chosen bitslip 0, read tap 4 (eye 0..9)` = 10 taps, against the recorded
    bring-up tuple of tap 8 / eye 17 wide, plus
    `WARNING: leveling not clean: ['final verify at centred (bitslip, tap) failed']`
    on every run. A marginal read eye is a CREDIBLE cause of a sporadic 1-2 beat
    miscapture with nothing to do with the scheduler. Do not assume the residue
    is a controller bug until this is explained. See
    [[project_pumice_board_bringup_tuple]].
 3. **Timing margin dropped +294ps -> +25ps.** The live gate sits in the
    final-pick cone, which is the known critical path. It CLOSES (post-phys-opt
    WNS=+0.025, TNS=0, hold met) but there is no headroom. Cheaper formulation
    available: because the DFI path is now constant-latency, the turnaround
    counter could be loaded AND checked at the selection stage, making spacing
    correct by construction and keeping the term out of the final-pick cone.

### 2026-09-17 ROUND 3: 90/90 CLEAN. Batching is correct and ON by merit.

The surviving gap-1 tRTW violation had a precise cause -- a ONE-CYCLE SEAM
between the two halves of the guard:

    r_rdfire0 <= w_fire_out && r_do_rd;   // records a fire the cycle AFTER it

but the pick that selects the next command is evaluated the cycle BEFORE its own
command fires. So a WRITE picked in the very cycle a READ fires out sees
r_rdfire0 still 0, and issues one cycle behind it. Neither half is wrong; they
simply do not overlap. Closed by folding the in-flight fire into the live gate:

    assign w_wr_turn_live = trtw_ok_i && !w_wr_turn_block
                         && !(w_fire_out && r_do_rd);

(w_fire_out is r_pick_valid && cmd_ready_i -- registers and an input, never the
combinational pick, so it cannot form a loop. Verilator confirms: no UNOPTFLAT.)

**Board, 30 reps x 3 watermarks x 4000 txn, gap 4, 1+1 -- 90 runs:**

    hi=0 (off)   0/30 failing   400.3 MB/s   <- control
    hi=2/lo=1    0/30 failing   449.3 MB/s   +12.2%
    hi=8/lo=4    0/30 failing   449.3 MB/s   +12.2%

Zero mismatched beats anywhere. **PUMICE-039's corruption is FIXED**, and write
batching -- the feature that could never be enabled -- now runs clean and pays
+12.2% bus bandwidth.

**The whole arc, every step measured at the wire, not inferred:**

    stage                  tRFC viol   idle-bus beats   tRTW viol   failures
    original                       1              180           -   2/8, 1/8
    + DFI constant-latency         0                0           4   10/10
    + live turnaround gate         0                0           1   3/30, 5/30
    + in-flight fire in gate       0                0           0   0/30 x3

Three distinct defects, each real, each pre-existing:
 1. tRFC: the DFI layer's own pacer stalled the in-order FIFO, compressing
    REF -> ACT from 15 cycles to 3. The DRAM discarded the ACT, the bank never
    opened, 180 consecutive reads captured an undriven DQ bus.
 2. tRTW classify-time staleness: the column masks gate ~3 pick-pipeline cycles
    before issue, so a write selected while no read had recently fired issues
    INTO a read burst that started meanwhile.
 3. tRTW one-cycle seam: as above.

(2) and (3) were latent for as long as the DFI pacer existed -- it masked them.
Sean's architecture call ("the dfi layer should be super simple, all delays come
from the scheduler") is what made them observable. A masked bug is strictly
worse than an open one: it moves under you the moment anything downstream
changes, which is exactly what PUMICE-042's tRTW=20 did.

**Corrected along the way, for the record:** the residue was NOT the read eye.
The bad beats carry a Hamming distance of 36/64 against expected -- random data
from a DQ collision, not a marginal capture. The eye anomaly below is real but
was never the cause.

### STILL OPEN after the fix

 1. ~~**Timing margin is +16 ps** -- refactor needed~~ **ACCEPTED, NOT A
    BLOCKER.** Sean 2026-09-17: *"this is designed for aggressive timing."*
    pumice is a research MC deliberately pushed hard (see
    [[project_pumice_at_rest]]), and a thin positive margin is the intended
    operating point, not a defect. Post-phys-opt WNS=+0.016, TNS=0, hold met --
    it CLOSES, which is the bar. The selection-stage / output-register refactor
    is recorded below for whoever wants the slack back, but nothing is waiting
    on it and it should not be treated as outstanding work.
 2. **Read eye is 10 taps (0..9, tap 4) against the recorded bring-up tuple of
    tap 8 / eye 17**, with `leveling not clean: final verify at centred failed`
    on every run, reproducibly. Not causing the corruption (see above) but
    unexplained and a real deviation from [[project_pumice_board_bringup_tuple]].
 3. ~~**PUMICE-043** should be re-tested~~ -- DONE 2026-09-17, and it WAS this
    same seam. Retested at its exact point (hi=8/lo=4, gap 15) with 30 reps:
    **0/30 failing** (1.8% chance of a false clean at its 12.5% rate).
    PUMICE-043 CLOSED. Its drain-depth dependence was the number of direction
    crossings, not accumulation over the run.
 4. `pumice_cmd_history_checker` still watches the ARBITER OUTPUT, which is why
    it reported zero tRTW violations throughout while the wire was violating it
    four times per capture. Retarget it at the DFI wire.

### 2026-09-17 BREADTH: 0 failures in 120 runs across the configuration space

The 90/30-clean result above was ONE operating point (gap 4, 1+1). PUMICE-037's
history is exactly a fix that held at the tested points and failed elsewhere, so
the fix was re-measured across 5 gaps x 2 generator counts x 3 watermarks,
4 reps = 120 runs:

    gens  gap |      off     hi=2     hi=8 |   gain2   gain8 | fails
       1    0 |    550.3    550.5    550.7 |   +0.0%   +0.1% | 0/12
       1    4 |    400.6    448.3    448.2 |  +11.9%  +11.9% | 0/12
       1    8 |    300.7    335.1    379.9 |  +11.4%  +26.3% | 0/12
       1   12 |    240.7    314.1    286.8 |  +30.5%  +19.2% | 0/12
       1   15 |    209.3    263.0    258.0 |  +25.7%  +23.3% | 0/12
       2  0-15|    160.7    163.0    163.0 |   +1.4%   +1.4% | 0/12 each

    TOTAL: 0 failing runs out of 120   (210 clean runs counting the 90 above)

Includes gap >= 8, which is PUMICE-037's regime, and 2+2, a different
arbitration pattern (more same-direction work queued, fewer turnaround
crossings).

**The performance characterisation is UNCHANGED from the pre-fix measurements,**
which is the check that matters: the fixes removed corruption without perturbing
the scheduler's throughput behaviour.
  * gap 12, 1+1 = **+30.5%**, against the "+30.6% at 1+1" recorded earlier in
    this task from the original (corrupting) measurements. Same number, no
    corruption.
  * 2+2 flat at ~163 MB/s at EVERY gap, against the recorded "~0% at
    2+2/3+3/4+4, bus plateaus at ~160 MB/s" -- multiple generators already keep
    same-direction work queued, so there is no turnaround left to amortise.
  * gap 0 shows no gain, the expected control: no read gap, nothing to batch.

**PUMICE-039's data corruption is CLOSED on evidence.** What keeps the task open
is the +16 ps timing margin (item 1 above), not correctness.

**Refactor note (for item 1).** The obvious approach -- mirror `r_tccd_fwd` and
load the turnaround counter at SELECTION -- does not transfer directly: tCCD is
direction-AGNOSTIC and loads the same value whichever column wins, whereas a
turnaround counter must know whether a read or a write was selected, and at that
stage BOTH can be candidates with the winner decided downstream. Loading on a
guess is wrong; loading conservatively (block both directions for max(tRTW,tWTR))
would throttle reads behind tRTW=20 and destroy read bandwidth. Two workable
options: (a) replicate the arbitration tie-break at selection, or (b) hold the
arbiter's OUTPUT REGISTER when the registered command would violate turnaround --
which keeps the term out of the pick cone entirely and is safe here precisely
because the DFI path below is constant-latency and cannot compress what it
receives. (b) is simpler and should be tried first.

## PUMICE-045 — one unattributed mismatched beat, seen once in 1008 matrix cells
### 2026-09-23: re-examine -- batching is now a candidate explanation

This beat was recorded as "unattributed" and was the evidence used to re-enable
write batching by default (`1f6a3bfdf`). Batching has since been shown to
STARVE READS outright ([[PUMICE-039]], fixed in `fc83c1b3c`), so "not clearly
attributable to batching" no longer holds as a reason to discount it. Re-check
against the bounded drain before treating this as noise.

**Status:** open 2026-09-18  **Priority:** P3
**TITLE AND PREMISE CORRECTED 2026-09-18: it does NOT break refresh_credit, and
it is not reproducible. See the repeat data below before acting on this.**

Enabling `SCHED_WR_WM` (2/1) by default broke exactly one cell of the 14-config
board matrix. Measured both ways on the same bitstream, same session:

    batching ON  (2/1) : 251/252   refresh_credit/incremental_bl16  FAILS
    batching OFF (0/0) : 252/252   zero non-OK cells

It is specific on BOTH axes:
  * 13 of 14 configs pass `incremental_bl16` -- only `refresh_credit` fails;
  * `refresh_credit` passes its own `incremental_bl4` and `incremental_bl8`.

So it is the interaction of the write drain with the refresh-CREDIT policy at
the longest burst, not batching generally and not bl16 generally.

**The default has been reverted to 0/0** (opt-in) until this is understood --
"on by default" has to mean safe everywhere. The feature itself is correct:
PUMICE-039's three defects are fixed and it measures clean over 210 runs at
open_page, worth +11.9%..+30.5%. Enable per-run with `TEST_WR_HIGH_WM=2
TEST_WR_LOW_WM=1` or by writing SCHED_WR_WM.

**Process note, recorded because it is the actual lesson:** the default was
changed on evidence from ONE config (open_page) and shipped to all fourteen.
The matrix that caught it should have been run BEFORE the change, not after.
Any future default flip on a config-selectable knob needs the full matrix first.

### CORRECTION 2026-09-18 -- not reproducible, not attributable

The original entry (written from ONE matrix) claimed batching breaks
refresh_credit at bl16. Repeating the full 14-config matrix three more times
with batching ON:

    original matrix : 1 non-OK   refresh_credit/incremental_bl16
    rep 1           : 0 non-OK   (252/252, zero mismatched beats)
    rep 2           : 0 non-OK   (252/252, zero mismatched beats)
    rep 3           : 0 non-OK   (252/252, zero mismatched beats)
    ------------------------------------------------------------
    batching ON     : 1 mismatched beat in 1008 cells

It did not recur in the 756 cells after it. The failure signature was ONE beat
of 64000 transactions (8.2 MB), with wr/rd bandwidth, utilisation and latency
IDENTICAL to the passing run to 3 significant figures -- batching perturbed the
traffic by 10 and 35 cycles out of ~19.5M. Nothing about that says "refresh
policy".

**So the premise is withdrawn.** One event in 1008 cells attributes to neither
refresh_credit nor batching. The batching-OFF comparison is a SINGLE 252-cell
matrix (0 non-OK), which at this rate is not evidence of a difference either --
matched repeat counts would be needed to claim batching is implicated at all.

**Process note, and the actual lesson of this task:** the default was flipped on
one config's evidence, then REVERTED on one matrix's evidence. Both directions
were decided at n=1. The repeats should have come first in both cases.

**What is still worth doing** (independent of this event):
`refresh_ctrl.sv` has no headroom between demanding a refresh and losing one.
While busy, `w_req = (r_pending > w_post_eff)` with post_eff clamped to 7, so
the request asserts at pending == 8 -- which is exactly MAX_PENDING, where
`else if (pend_n < MAX_PENDING)` stops incrementing and further tREFI ticks are
silently dropped ("saturate (data retention violation looming)"). The threshold
to START asking and the threshold to BEGIN LOSING refreshes are the same number,
so any grant latency past that point costs real refreshes. Worth fixing on its
own merits; it is NOT established as the cause of anything above.

**Original starting hypothesis, kept for reference but NOT supported:**
refresh_credit is the only refresh policy that banks credits
rather than pacing refreshes at a fixed interval. A long write drain delays the
refresh the credit scheme is counting on, so the suspect is drain length vs
credit accumulation -- which also explains why only the LONGEST burst fails.
Reproduce with `--profile full` and TEST_WR_HIGH_WM=2, then narrow with the ILA
on REF spacing during a drain (the tRFC decode in reports/ already does this).
