<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

## PUMICE-033 — one extra AXI ID bit doubles the arbiter's pick cone
**Status:** open 2026-09-14  **Priority:** P1 — it is a hard constraint on where pumice can be used

**The finding: `AXI_ID_WIDTH` 8 -> 9 takes the arbiter's
`r_rd_pop -> r_wr_col_q` path from 13 logic levels to 26, and 75 MHz from
+1.100 ns to -6.602 ns.** Measured at SYNTHESIS, before placement, so it is the
netlist and not congestion. Same RTL, same constraints, same clocks, same
synth settings; the only difference is the parameter.

| ID width | logic levels | data path delay | post-route slack |
|---|---|---|---|
| 8 | 13 | 11.09 ns | +1.100 |
| 9 | 26 | 20.21 ns | -6.602 |

**Why it matters beyond this board.** BRIDGE-016 made fabric IDs
`{master index, master id}`, so ANY multi-master fabric in this repo hands its
slave more ID bits than a single master drives. pumice cannot currently absorb
that. It is usable behind one master, or behind a fabric that keeps the index
inside the master's own width -- which is what the char harness now does, by
putting the generator index in the top bits of the 8-bit id rather than on top
of it (7baf98780). That works and costs 1 bit of id space per doubling of
masters, but it is a workaround in the CONSUMER, not a fix in pumice.

**Where to look.** `pumice_cmd_arbiter.sv`: the pick is
`NUM_ENTRIES`-wide and ID comparisons are replicated across every entry, so an
extra bit multiplies by the entry count rather than adding to it. `qos_top` at
:818 is the same shape. The fix is presumably to compare a narrowed key, or to
pipeline the pick a stage further, not to widen everything and hope.

**How this was found**, because the route to it was wrong twice and the method
is the reusable part: the regression was first blamed on removing the data
bridges, on the read-return-ring depth, on constraints, on placement directives
and on hierarchy flattening -- each ruled out with its own build. Sean rejected
the bridge explanation on the grounds that generators behind a bridge and
generators without one look identical to pumice, which is correct and is what
forced the measurement that found it. **Logic levels at the synthesis
checkpoint are the discriminator**: if they differ between two builds, the cause
is RTL or parameters and can never be placement.

```
open_checkpoint <run>/synth_1/<top>.dcp
report_timing -to [get_pins -hier -filter {NAME =~ *u_arbiter/r_wr_col_q_reg*/D}] \
              -max_paths 1 -path_type full
```

**Definition of done:** pumice closes 75 MHz with `AXI_ID_WIDTH = 9`, or the
constraint is documented as permanent in the HAS with the id-space workaround
named as the supported pattern.

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
**Status:** open 2026-09-10  **Priority:** P1 — the largest identified defect left

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

## PUMICE-028 — the pumice sim has never run the board's DRAM geometry
**Status:** open 2026-09-10  **Priority:** P1 — this is why a 2x read throttle shipped green

`dv/tests/top/test_pumice_core_dfi.py` ran at DRAM_BEAT=64 / BL8 / device==beat,
so **one DRAM burst is 4 AXI beats**. The board is DRAM_BEAT=32 / BL4 / x16,
where **one DRAM burst is 1 AXI beat**. Any per-sub-command rate limit is
therefore divided by four before a bandwidth assertion can see it: the read
intake's admit gate (PUMICE-025, fixed) supplied 2 beats/cycle at the sim
geometry and looked healthy, while on the board the same gate WAS the
bandwidth. Every read/write ceiling test passed throughout.

The geometry is now env-overridable (`TEST_DRAM_BEAT` / `TEST_DRAM_BL` /
`TEST_DRAM_DEVICE_W`, defaults unchanged) and `pumice_core_tb_top` takes
`DRAM_DEVICE_WIDTH`. **But the board point does not yet run clean**, so it is
not wired into the suite:

- `read_ceiling` at board geometry trips `pumice_dfi_rd_return_checker` --
  "32 reads outstanding for 512 cyc with no return".
- `write_ceiling` at board geometry stalls W for 1409 cycles (max run 19),
  while the real board sustains 95% of peak on writes. So the failure is the
  testbench or its DFI model, not the DUT.

**Do:** make `TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16` a clean,
routinely-run configuration of the core suite (the write ceiling is the
control: it must reproduce the board's ~95%), then add it to the regression so
board geometry is covered by default. Until then `[[project_pumice_char_suite]]`
board numbers are the only place these limits are visible.

**Why it matters:** the handbook rule is already "match the FPGA exactly in
sim"; this is the case that proves the cost of not doing it. A suite that
cannot express the shipping geometry cannot gate it.

---

## PUMICE-006 — QoS + advanced scheduling (post-cleanup)
**Status:** MECHANISMS COMPLETE 2026-08-27 — all three axes implemented
(Axis 1 scheduling, Axis 2 paging, Axis 3 refresh), every mode OFF by
default and mutation-proven. Characterization/tuning split to
[[PUMICE-013]]. Holds open only for mechanism gaps 013 reports back.

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
**Status:** open 2026-08-27 (split out of PUMICE-006 at Sean's direction —
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
2. The measurement path is changing underneath it: the bespoke harness
   meters/hists are being retired for the external observer
   ([[PUMICE-016]]), and the 1:1 accounting check moves with them. Land
   016 first or the numbers carry the AMBA-HISTCH1 accounting error.
3. The interesting telemetry already exists in-controller and should be
   the primary signal per Sean's direction (cheap counters stay in
   pumice): PAGE_STATS hit/miss/empty, SCHED_STATS act/pre,
   REF_STATS_REF, OBS_ROW_HIT per bank, refresh-defer histograms.
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

## PUMICE-016 — adopt axi4_intf_master_observer (APB-configured) for perf observation
**Status:** ACTIVE 2026-08-26 — now the DIRECTED path, not a nicety.
Sean's direction: "don't have any monitor logic or perf logic inside
pumice — I have an external block that does just this. However, keep
tracking things like paging results and anything else that is easy but
interesting." So: the char harness's hand-rolled bus meters + latency
hists are to be RETIRED in favor of this observer (which also sidesteps
the AMBA-HISTCH1 shared-primitive bug the bespoke path sits on — the
observer instantiates the hist at NUM_CHANNELS=8); pumice keeps only the
cheap counters (PAGE/SCHED/REF *_STATS, OBS_ROW_HIT, refresh-defer
histograms). PUMICE-020 closed onto this task; the 1:1 accounting check
moves to the observer path when it lands.

pumice rolls its own perf observation: `perf_rd_prod/bp/starv/idle`,
`perf_rd_hist_count/total`, `perf_clear`, `perf_freeze` wired out of the harness
and read back through harness CSRs. The stream flows use
`axi4_intf_master_observer`, an inline pass-through meter over the same primitives
(`axi_bus_meter`, `axi_perf_latency_hist`) that also emits monbus packets.

**What changed that makes this worth doing (2026-08-04):** the observer now
carries its OWN APB config regblock (`obs_regs`) instead of exporting 29 `cfg_*`
ports for the instantiating harness to tie off, and it moved to
`projects/components/misc/rtl/` so it is reachable from any board flow:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f

So adopting it costs one bridge APB slave and one instantiation, not 29 tie-offs
and a harness that has to know the block's internals. Registers are by name via
the generated regmap (see [[registers-by-name]]).

**Why bother:** pumice and stream currently measure throughput with different
code, so their numbers are not strictly comparable — which matters because the
pumice-vs-LiteDRAM A/B and the stream characterization both report MB/s. One
meter means one definition of a stalled cycle, and pumice would inherit the
latency histogram and the monbus packet path for free.

**Scope note:** the observer is an AXI4 pass-through meter (it was called
`axi4_dma_observer` until 2026-08-04; the DMA in the name was always wrong). pumice's interesting
traffic is on the DFI side, so this covers the AXI front-end (host -> pumice_top)
rather than DRAM-side behaviour; the DFI meters stay as they are.

**Not urgent.** Do it when the pumice harness is next opened for other reasons,
not as a standalone change — it touches the bridge map and the harness CSR
readback, and pumice bitstreams are on the critical path for the DDR2 work.

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

## PUMICE-037 — concurrent read+write with reader gap >= 8 returns bad data AND corrupts cells
**Status:** open 2026-09-14  **Priority:** P0

Found while running PUMICE-036 on the board (4+4 bitstream, 75 MHz, BL4, x16,
`open_page`). It is a correctness defect, not a performance one, and it is the
reason the first `bank_gap_sweep` run looked incoherent.

**The trigger, narrowed by elimination on hardware:**

| configuration | result |
|---|---|
| prefill 128 MiB, then read every bank read-only, all 3 families | CLEAN |
| reader ALONE, gap 0..15 | CLEAN at every gap |
| writer ALONE, gap 0..15 (incremental, marches all banks) | cells CLEAN |
| writer gap 0..15, **reader gap 0** | CLEAN at every writer gap |
| **reader gap 0..7** + concurrent writer | CLEAN |
| **reader gap >= 8** + concurrent writer | 1.5k-7k of 32000 beats mismatched |
| 4+4 concurrent, gap 0 (and gap 4), incremental | CLEAN, cells CLEAN |

So it needs BOTH a concurrent writer AND the reader's gap field at 8 or above.
Neither engine alone does it at any gap, and the writer's own gap never does it.

**Two distinct symptoms, and the second is the serious one:**
1. *Transient* — with writer and reader on disjoint banks (row_major, writer
   confined to bank 0, reader to bank 4) the reader reports thousands of
   mismatched beats, but a read-only audit of all eight banks afterwards is
   CLEAN. The cells were always right; the returned data was not.
2. *Persistent* — with writer and reader ranges OVERLAPPING (incremental) the
   audit afterwards shows real DAMAGE: banks 3/4/6/7 dirty, 248..4636
   mismatched beats each, reproducible on re-read. Cells genuinely hold wrong
   data. **The write engine alone never does this** (verified above), and a
   read engine cannot write, so something in the concurrent path is either
   writing the wrong data or writing it to the wrong address.

**Why the first sweep run was unreadable.** Damage from one point is inherited
by every later point. `row_major g1` reported an identical 3694 mismatched
beats at eight consecutive gaps; that constant is the *previous* family's
damage being re-read, not a property of those points. Confirmed directly: a
later row_major point reported exactly 5025, which was precisely the audited
mismatch count of bank 4 going in. `bin/bank_gap_sweep.py` now re-fills the
device before every point (`PREFILL=point`, the default) so points are
independent.

**Not yet determined: whether this is pumice or the harness.** Both are live:
- *Harness read engine* — in `axi4_master_rd_crc_check.sv` the R-beat
  bookkeeping (`if (w_r_beat)`, ~line 707) sits inside the `S_RUN` arm, while
  the mismatch compare at the bottom of the same block runs unconditionally.
  A beat that lands while the FSM is in `S_GAP` is compared but not counted.
  **Measured and largely RULED OUT.** That path can only fire through the
  stray-beat drain (`fub_rready = w_r_consuming || w_stray_beat`), and the
  sweep now records `o_stray_beats` per reader: **every one of the 22 failing
  points reports stray = 0**, across 192 points. No beat was drained without an
  owner, so the mismatching beats were legitimately outstanding and came back
  with the wrong DATA. That is a controller-side answer, not a bookkeeping
  artifact — and it is consistent with symptom 2, which the read engine could
  never have produced anyway.
- *pumice* — symptom 2 points at the controller under mixed R/W. Note the
  known refresh-collision suspicion in [[project_pumice_board_bringup_tuple]].

The sharp edge at exactly 8 (bit 3 of the 4-bit gap field) is unexplained; the
gap logic in both engines is a plain 4-bit countdown with nothing special at 8,
and the register layout has gap[27:24] with nothing adjacent.

**Sim repro IMPLEMENTED 2026-09-14 — and it does NOT reproduce.**

`test_ddr2_char_macro.py::test_ddr2_char_macro_concurrent_gap`, ten points:
rd_gap 0/4/7 (control, below the board's edge), 8/12/15 (at and above it),
wr_gap 8/15 at rd_gap 0 (the writer-only isolation the board measured clean),
and 8/8, 15/15 (the sweep's own failing shape). Writer on bank 0, reader on
bank 4, wrapped in one page each, ONE `go(wr_mask, rd_mask)` for both — the
board's `start_both`. **All ten pass.**

The test is armed, not decorative: giving the reader a wrong LFSR seed fails
all ten with "reader 0 data error", and restoring passes all ten. That
mutation was run at the shipped configuration, not a convenient one.

So the sim does not see it **at this geometry**, which is the substance of
[[PUMICE-028]]: this build is `DRAM_BL=8` where the board is BL4, so one DRAM
burst is 2 AXI beats here against 1 on silicon. The next step is no longer
"write the test" — it is running this test at the board's geometry, and
PUMICE-028 records that the board point does not yet run clean in sim.

**Driven at pumice_top too 2026-09-14 — also does NOT reproduce.**
`test_pumice_top_concurrent_rw`, 32 points, all clean. Writer and reader in
flight together on disjoint banks, reader pacing itself between bursts, with
the golden MemoryModel checking BOTH symptoms separately (read beats vs golden
= "bad data"; written cells vs what was written = "corruption"):

| axis | values swept | result |
|---|---|---|
| reader gap | 0, 4, **8**, **15** | clean |
| geometry | bl8 sim point, **bl4x16 board** | clean |
| DFI read latency | 2, **7** (board tuple rden 6 / rddata_delay 7) | clean |
| refresh | default, tight (forces refresh INTO the traffic) | clean |
| reads in flight | 1, **32** (board depth, engine-style B2B ARs) | clean |

Armed, verified twice: corrupting the expected value fails and names the
address, and a permanent count guard asserts the reader compared
`n x BL_WORDS` beats — a concurrent test that returns zero beats would
otherwise pass vacuously.

**Read concurrency was the leading hypothesis and it is now TESTED AND DEAD.**
The first cut of this test used the default sequence runner, which serialises
each burst against its own response and caps outstanding at ONE -- so the gap
always landed on an empty pipe and nothing could ever be in flight across it,
which is precisely the state an `S_GAP`-class hazard needs. Sean: "the bfms
fully support b2b cycles". Re-driven through `run_axi4_sequence_engine`, which
queues ARs back-to-back with no per-burst response wait, at the board's depth
of 32. Still clean.

The depth axis is real, not decorative -- measured, not assumed: depth 1 gives
64 groups and 40990 ns of sim, depth 32 gives 2 groups and 30000 ns, both
comparing the same 64 beats.

**So it is not the controller, across every board-faithful axis inside it:**
geometry, read latency, refresh, and read concurrency. Four rounds of "add an
axis, still clean" says the search space is wrong, not under-sampled.

**Everything still untested is OUTSIDE pumice_top** -- `char_gen_unit`'s N:1
merge and boundary skids, the geared wrapper's dwidth converters, and the real
a7ddrphy against a real device. The board traverses all three; none of these
sims do.

---

### CAUGHT ON THE BOARD WITH AN ILA, 2026-09-14 — it is PHY-side, not the AXI return path

Sim could not reproduce it, so the defect was captured where it lives.
`reports/ila_mism.csv` (4097 samples, 394 mismatching beats in one window).

**How.** `char_engine_block` already exposed a per-beat debug stream --
`rd_dbg_valid / actual / expected / mismatch` -- that was never wired to the
top and whose FIFO defaulted to depth 0, so nothing had ever used it.
Threaded `RD_DBG_FIFO_DEPTH` through the harness and top (default 0, so the
production bitstream is unchanged), `mark_debug`ged the stream, and added a
`mism` trigger mode to `capture_ila.tcl`. **Triggering on the corruption
itself** is the whole point: every other trigger fires on normal traffic, and
at this error rate a free-running capture is a lottery that would not say
which beat lost. ILA build closes at **WNS +0.010 ns, 0 failing endpoints**,
so the capture is trustworthy.

**What the failing beats look like:**

| | |
|---|---|
| mismatching beats captured | 394 |
| `actual` == `ffffffffffffffff` (all-ones) | 233 (59%) |
| `actual` == all-zeros | 0 |
| other (genuinely different data) | 161 (41%) |

All-ones with zero all-zeros is the signature of an **undriven DQ bus** -- a
read whose capture window missed -- not of a mangled datapath.

**The corruption is already present at the DFI boundary.** Baseline all-ones on
`w_dfi_rddata` is 1.6% of samples, and with GOOD beats in the same capture as
the control:

| | within 11 cycles of an all-ones on the DFI bus |
|---|---|
| FAILING beats | **82%** |
| GOOD beats | **30%** |

So pumice's return path is faithfully delivering what the PHY handed it. That
moves the defect from the controller's AXI/return logic to the PHY read
capture, and is consistent with 32 clean points at `pumice_top` -- the sim's
DFI slave BFM always returns correct data, so no controller-level test could
ever have seen this.

**Write-to-read turnaround is RULED OUT as the mechanism.** It was the obvious
hypothesis from the waveform (writes sit a few cycles before the failing
reads), and the control kills it: within 4 cycles of a `dfi_wrdata_en`,
FAILING 59% vs GOOD 59% -- no discrimination at all. At 7 cycles it is 81% vs
67%, which is weak and not worth building on. Do not re-open tWTR/tRTW on this
evidence.

**Read-eye narrowing under write load is RULED OUT (2026-09-15).** It was the
natural follow-up to the all-ones signature and it is wrong. Tap sweep at the
operating bitslip, quiet vs with three background writers hammering other
banks, load VERIFIED in flight on every row (`gen_done` checked after each
read, printed per row):

| tap | quiet | loaded |
|---|---|---|
| 0-9 | clean | clean |
| 10 | 3055 mismatched | 3034 mismatched |
| 11-13 | 4096 mismatched | 4096 mismatched |

Same eye edge, same counts. Write traffic does not move the read eye, so the
corruption is not read-capture margin against bus loading.

**Three earlier attempts at this measurement were WRONG and are recorded so
nobody repeats them.** The first reported "no passing tap when loaded" -- an
eye collapse -- and it was an artifact: it armed the load and then called
`_test()`, which begins with `_reinit()` (a soft reset) and stops it. The
second had the same ordering bug. The third died on a bad API call. Worse,
each left `TXN_MAX` writers running, and **a runaway generator survives
`soft_reset`** ([[feedback_runaway_generators_survive_soft_reset]]): the next
run's leveling reported "no passing tap at ANY bitslip -- analog read path not
recoverable, check sys4x_dqs / IO / pins", which reads as dead silicon. The
board was fine; a reprogram plus re-level gave `verify OK` immediately. Only
reprogramming clears a runaway.

### NOT all board tests fail -- 11%, and the failing ones share three traits

Sean asked the right question: do ALL board tests fail? They do not. Of the
192-point sweep, **22 points (11%) mismatch**; `axlen_sweep` and
`outstanding_sweep` are entirely clean. The failures are sharply structured:

| trait | failing points |
|---|---|
| generator count | n_gen **1 (19) and 2 (3)** -- never 3 or 4 |
| address order | incremental (14), row_major (8) -- **col_major NEVER** |
| gap | mismatches rise MONOTONICALLY: 80 / 122 / 435 at gaps 1/3/6, then ~5000 from gap 8 |

col_major is the page-MISS family: every burst activates a different row, so it
can never hold a stale belief about an open one. The two families that DO fail
are page-HIT streams, where a gap leaves a row **open and idle** between bursts.

### RETRACTED: it IS a refresh collision (Sean was right, 2026-09-15)

The section below concluded "not refresh" from an invalid experiment, and the
ILA trace refutes it. **Both of my arguments were wrong:**

1. *"Rare refresh is no better, so refresh does not drive it."* tREFI 32767 MC
   cycles at 75 MHz is **437 us** between refreshes against a JEDEC tREFI of
   7.8 us. That run was not testing a refresh collision, it was violating DRAM
   RETENTION -- those 62439 mismatched beats are decayed cells, a different
   failure wearing the same symptom. The experiment could not have answered the
   question it was asked.
2. *"Close page fixes it, so it is the open page."* Backwards. Close page
   removes the open-row state that a refresh would invalidate, so close page
   fixing it is evidence **FOR** a refresh collision, not against it.

**The trace, from the capture already committed** (`reports/ila_mism.csv`,
window around the refresh at sample 2551):

```
 2538  RD  bank4          reads issued to bank 4
 2539  RD  bank4
 2540  RD  bank4
 2546  PRE bank0
 2547  PRE bank4      <-- bank 4 precharged 7 cycles after its reads
 2551  REF            <-- refresh
 2568  ACT bank4      <-- row re-activated 17 cycles later
 2575  RD  bank4          reads resume
```

`rd_dbg_mismatch` is asserted CONTINUOUSLY from 2530 to 2579 -- the entire
window from the reads, through the precharge and refresh, until well after the
re-ACT. The refresh's precharge lands on a bank with reads still in flight
through the PHY, and everything in that window comes back wrong. All-ones is
what an undriven DQ bus reads as, which is the 59% signature.

Three of the five refreshes in the capture show the clean pattern
(REF -> ACT bank4 +17 -> ACT bank0 +23 -> RDs +24); the mismatch clusters are
the ones where reads were already outstanding when the refresh arrived.

**This also explains every trait of the failure distribution** without needing
the open-page argument to be about page policy per se: col_major never fails
because it precharges per access and has no in-flight window for a refresh to
collide with; the gap dependence is monotonic because more idle means more
chance a refresh lands mid-flight; low generator counts fail because the read
pipeline is sparser.

### Correct refresh programming does NOT fix it (2026-09-15)

Two separate refresh problems, and only one of them is PUMICE-037.

**Problem 1, real and now fixed: the host had the clock wrong.**
`pumice_char.Config.mc_clk_hz` defaulted to 100 MHz; the board measures
**72 MHz** (bus meter: 233,964,081 cycles in 3.248 s). Every JEDEC timing was
converted into cycles for the wrong clock. Most land conservative at a slower
clock -- a cycle count for a faster clock buys MORE real time -- but tREFI
inverts: 780 cycles is 7.8 us at 100 MHz and **10.8 us at 72 MHz**, against a
JEDEC MAXIMUM of 7.8. The part was under-refreshed ~38% for this entire
investigation. Fixed in `bfcff909d`, with `measure_mc_clk_hz()` /
`check_mc_clk_hz()` so a host can ask the board instead of being told.

**Problem 2, still open: that was not the cause.** Same workload, open page,
`incremental`, 3 repeats, beats mismatched PER RUN:

| refresh programmed for | gap 8 | gap 12 |
|---|---|---|
| 100 MHz (wrong, tREFI 10.8 us) | 5727 | 1959 |
| 75 MHz (correct, tREFI 7.8 us) | 5158 | 2790 |

3/3 runs fail either way and the rates are the same to within run-to-run
scatter. **Correcting the refresh interval does not suppress the corruption**,
so the under-refresh was a genuine misprogramming sitting on top of the defect,
not the defect. (row_major was still running when the window closed; incremental
alone settles the question.)

That leaves the collision itself as the defect: pumice issues precharge + REF
while reads are in flight, and tREFI only sets how OFTEN that window comes
round, not whether it corrupts when it does.

### The aligner DOES capture the PHY preamble -- but fixing it is not viable, and it is not the board defect

Sean: "We had rd alignment there before but an earlier Claude removed it." The
history is exactly that. Three fixes landed and were reverted within an HOUR on
2026-07-14 (2f08eb23e/f0354c137, dcaedce4b/39827800a, 144b3860f/19d483880), and
79a848b69 replaced them with the multi-outstanding redesign, which gates
capture on `r_outstanding != 0` -- its own comment calls that "a WIDE
admit->return gate".

**The defect is real and now has a test.** `cocotb_test_rd_aligner_phy_preamble`
injects what the 2026-07-14 ILA saw: a `dfi_rddata_valid` one cycle BEFORE the
enable window with the device not driving DQ. The aligner captures it, because
the read IS outstanding at that moment and a wide gate cannot exclude it.
`rd_last` then fires a word early and the whole read stream shifts. Nothing in
the suite had ever injected a preamble, so this had never been tested either
way.

**But the fix is not viable, and this is why it keeps being reverted.**
Restoring 2f08eb23e's enable-window credit (+1 per enable cycle, -1 per
captured word):

| check | result |
|---|---|
| rd_aligner unit suite | 4/4 pass |
| full pumice fub+macro+top | 274 pass / 0 fail |
| board bitstream at 75 MHz | builds, **WNS +0.055 ns** (better than the +0.016 without it) |
| `test_ddr2_char_uart` a7gated cases | **2 passed WITHOUT the fix, 2 FAILED WITH it** (direct A/B, clean build each way) |
| board corruption, gap 8 | 5158 -> 4795 beats/run -- **inside run-to-run scatter** |
| board corruption, gap 12 | 2790 -> 2020 beats/run -- same |

So it breaks a previously-passing path AND does not reduce the corruption. The
July reverts were almost certainly this same wall, hit three times in an hour.

RTL reverted. The test stays as `xfail(strict=True)` so the preamble capture is
documented, reproducible and impossible to lose again -- and flips to XPASS the
moment a viable fix lands.

**What this leaves.** The preamble capture is a genuine bug that needs a fix
compatible with the a7gated path -- look at what those two tests model before
attempting another credit scheme. And PUMICE-037 itself is still open: the
aligner preamble is NOT its cause.

### RETRACTED: the scheduler-layer "reproduction" was a FALSE POSITIVE

The section below claimed `PRE(bank 4) issued 1 cycles after RD, tRTP=2` and
named a stale-registered-readiness hole in `w_rfsh_pre_found`. **All of it was
wrong.** The scheduler TB did not stamp cycles on captured commands and the
helper fell back to the LIST INDEX, so "1 cycle after RD" actually meant "PRE
was the next COMMAND in the stream" -- a statement about ordering, not timing.
It nearly drove an RTL change to code that was already correct: `r_guard0` IS
set on a fired column (`pumice_cmd_arbiter.sv:1282` includes `r_do_rd`) and
`w_rfsh_pre_found` DOES gate on `!w_guarded[j]`.

`_cmd_sink` now stamps the issue cycle, and the helper asserts rather than
falling back to an index.

### The scheduler layer does NOT reproduce it -- two tests, both passing

| test | what it checks | result |
|---|---|---|
| `..._refresh_inflight_read` | tRTP from the last same-bank column, tRP into the REF | **spacing respects tRTP=2 tRP=3** |
| `..._refresh_read_stream` | every column lands on a bank with an OPEN ROW, across a sustained stream | **408 columns, 2 REF, all on an open row** |

The second is the one that matters: the first attempt had ONE read outstanding,
which is not the board's state. This streams reads continuously by re-arming the
mock CAM as each issues, so a refresh has to cut into a live queue -- 408
columns across 2 refreshes -- and models row state from the command stream
itself (ACT opens, PRE closes that bank, REF closes all, AP closes on the
column). Not one column is issued to a bank with no open row.

**So the command stream pumice generates is correct**, in both respects that
could produce the board's all-ones: spacing, and never reading a closed row.
That eliminates the scheduler and pushes the defect BELOW it -- the DFI layer's
phase packing and read-return alignment, or the PHY capture. Note the prior
VCD work already pointing there: commit 79fb58a66, "mask-removal corruption is
DFI read-return alignment".

(One more modelling trap recorded: a DDR2 column command carries the COLUMN, so
`cmd_row_o` reads 0 on RD/WR. Comparing it against the open row flags every
column -- 408 of 408 on the first run. Only the "is a row open" half is
checkable from the command stream.)

### Superseded: "REPRODUCED IN SIM at the scheduler layer"

`test_pumice_mem_cmd_scheduler_refresh_inflight_read` — no board, no PHY, no
data path:

```
PUMICE-037: PRE(bank 4) issued 1 cycles after RD to the same bank, tRTP=2.
The DRAM is precharged while its read burst is still being driven out.
```

The refresh path precharges a bank **one cycle** after issuing a READ to it,
against a programmed tRTP of 2. That is the collision, at the layer that
decides command spacing. It is kept as `xfail(strict=True)` so the suite stays
green and the test flips to XPASS the moment the RTL is fixed.

Why no earlier sim saw it: the char macro and `pumice_top` both hand the
controller a DFI slave that always returns correct data, so a truncated read
burst still reads back clean. Only a check on COMMAND SPACING can see it, and
that is what this layer owns.

**Candidate location, from the RTL's own reasoning.** The refresh-drain PRE
picks a bank via `w_rfsh_pre_found`, which gates on `r_bank_pre_ready` — a
REGISTERED copy of the bank-timer readiness (`pumice_cmd_arbiter.sv:533`). The
comment at :304 states the hazard exactly:

> "a column fired <2 cycles ago has not yet dropped this bank's registered
> pre_ready (tRTP/tWR load), so an unguarded PRE pick — normal or
> refresh-drain — could precharge on stale readiness."

`w_guarded` is the intended protection and covers columns in the PICK PIPELINE
(selection / pre-pick, plus the output stage via `w_inflight_col`). The failing
case is a column that has already ISSUED, where the only remaining protection
is that stale registered readiness. This is the same stale-registered-bank-image
family as [[project_pumice_scheduler_ceiling_rootcause]] and
[[project_pumice_mask_ap_hazard_and_tccd_csr]].

Note the REFpb (LPDDR2 per-bank) arm gates on
`r_bank_pre_ready[RK0][refresh_bank_i] && !w_guarded[...]` explicitly, while the
REFab arm relies on `w_rfsh_pre_found`. Whether that asymmetry matters is worth
checking, but it is NOT yet established — do not treat it as the diagnosis.

**What to look at:** whether the refresh scheduler drains (or blocks on)
outstanding reads before issuing precharge-all + REF. The standing suspicion in
[[project_pumice_board_bringup_tuple]] -- "residual corruption is a
refresh-collision bug" -- was right all along.

Close page remains a usable WORKAROUND (33725 beats -> 6), but it is a
workaround, not a diagnosis.

### Superseded: "it is the OPEN PAGE, and it is NOT refresh"

The obvious hypothesis was a refresh landing in that idle window, precharging
the bank while the tracker still believes the row is open -- which would
explain the all-ones. **Tested and REFUTED.** Six repeats per cell, because the
failure is intermittent (gap 12 and 15 failed in the sweep and came back clean
on a re-run, so single points prove nothing):

| config | gap 8 | gap 12 |
|---|---|---|
| open + refresh normal (tREFI 780) | 6/6 runs, 33725 beats | 0/6 |
| open + refresh RARE (tREFI 32767) | 6/6 runs, **62439 beats** | 0/6 |
| open + refresh FAST (tREFI 256) | 6/6 runs, 16529 beats | 6/6, 2759 |
| **close page**, refresh normal | 6/6 runs, **6 beats** | 6/6, **6 beats** |

Making refresh RARE does not help -- it is slightly WORSE -- so refresh rate
does not drive this. Page policy does: **close page cuts the corruption from
33725 beats to 6**, a ~5600x reduction on the identical workload. (Not zero:
about one beat per run survives, which is its own small question.)

So the trigger is an OPEN ROW left IDLE across the reader's gap, and the next
access to it returning undriven data. Refresh is ruled out as the mechanism;
what the controller does with a page it is holding open across an idle window
is not.

**Close page is a usable workaround** for anyone blocked by this, at the cost
of the open-page bandwidth.

**Next:** ILA again, but trigger on the mismatch with the DFI COMMAND bus in
the capture (ras/cas/we/bank/address are already marked) and read back the
command sequence before the failing beat: was an ACT actually issued for that
row, or did the read go out against a row the DRAM had already closed?

**Open and worth a look: the operating tap may be marginal.** `level_cache.json`
records the bring-up eye as `[0, 16]`, width 17, tap 8 centred. Today's scan
gives **0..9, width 10, with tap 8 ONE tap from the upper edge**. That is
either drift since bring-up or an artifact of test depth (more beats per tap =
more chances for a marginal tap to fail = a narrower measured eye). The
depth sweep meant to settle it was the run that hit the runaway, so it is
UNMEASURED. Re-run `txn` 16/64/256/1024 from a freshly programmed board.

**Next:** this is still a PHY read-capture question, so it belongs with the
leveling tuple ([[project_pumice_board_bringup_tuple]]: wrlat 1, rden 6,
rddata_delay 7, bitslip 0 / tap 8, eye 17 wide). Re-run the read-eye scan
WHILE a concurrent write stream is running -- the eye was characterised on a
quiet bus, and if it narrows under write activity that is the whole story.
`bin/` already has the leveling and eye tooling.

**Still recommended as the cheap partition:** run the failing
configuration with LiteDRAM swapped in for pumice. Both sit behind the
identical `char_engine_block`, and that A/B already localized the read ceiling
once ([[project_litedram_same_harness_ab]]). If LiteDRAM corrupts too, the
harness owns it and pumice is exonerated; if it does not, the defect is
pumice's and lives in something only the real PHY exposes. That is one board
run and it partitions the remaining space in half.

**Three pre-existing defects found while getting there** (all in
`dv/tests/top/test_pumice_top.py`, all fixed):
- The module read `BL` from env `"BL"`, a name nothing sets, while the runner
  exports `"DRAM_BL"` — so the Python side believed BL8 no matter what the RTL
  was built as. Harmless at the default where both formulas agree; at the board
  point it computes 2 AXI beats per burst where hardware has 1. That is
  [[PUMICE-028]]'s "overridable but never actually tested", made concrete.
- `BL_WORDS` used `BL // DFI_RATE`, correct only when device width == beat
  width. Now `(BL x device) / core`, matching `test_pumice_core_dfi.py`.
- The shared `sim_build` key was NUM_RANKS alone. A BL4 test would recompile
  the shared build out from under the BL8 suite in the same xdist worker,
  silently turning the tests that ran before it into tests of a different DUT.
  The key now carries every netlist-affecting parameter.

Geometry, read latency and refresh are pytest PARAMETERS now, not env knobs
(Sean, 2026-09-14) — an override nobody sets is how the board shape stayed
unrun.

**Three things the implementation had to get past, all worth knowing:**
- *Stale done.* The prefill leaves `gen_wr_done` high, so waiting on it
  directly returns instantly on the previous run and everything after inspects
  the PREVIOUS run's state. The first version "passed" a deliberately
  corrupted configuration in a quarter of the runtime. Fixed with
  `_wait_restart_done`, which waits for the restart to CLEAR done first.
- *ADDR_HASH does not compare in this build.* The board runs `data_mode=1`;
  in sim a reader given a deliberately wrong hash seed reports
  `beats_mismatched=0`, and so does one pointed at a page nobody wrote. Both
  mutations pass. The same mutations in LFSR mode fail loudly. Filed as
  [[PUMICE-038]] — **until it is fixed, a sim check written in data_mode=1 is
  decorative.** This test therefore uses LFSR.
- *LFSR + wrap must not revisit.* The wrap window holds
  `PAGE_BYTES/BURST_BYTES` distinct addresses; past that the walk revisits
  while the LFSR stream has moved on, so memory holds the last pass and the
  reader expects the first. Every point fails, controls included — a broken
  test, not a finding. The txn count is now capped to one pass and asserts it.
  (The board runs many passes because ADDR_HASH rewrites are idempotent.)

**The coverage hole is exact, and checked.** `test_ddr2_char_macro.py` has two
gap-bearing suites and BOTH drain the writer before the reader starts:
- `pacing_sweep_b2b` (~line 563) — `_start_writers` then
  `_wait_done(gen_wr_done)` then `_start_readers`.
- `ooo_pacing_schmoo` (~line 405, commented "Writes: preset memory") — same
  order, and its `_OOO_SCHMOO_STEPS` already includes `slow_same` at
  rd_gap=8 and `asym` at rd_gap=15.
So the gap values that fail on hardware are already in the matrix; what is
missing is running the two directions AT THE SAME TIME. The sim has never
exercised a reader gap with a writer still in flight, which is why this got to
the board. A new `test_type` that programs both and issues one concurrent
start — the board's `start_both` — should reproduce it directly.

**Second, smaller phenomenon, kept separate because it may be unrelated.** At
1+1 with the two ranges OVERLAPPING (cacheline), small mismatch counts appear
at some gaps BELOW 8 too -- 80 at gap 1, 122 at gap 3, 435 at gap 6 -- and
2+2 cacheline shows the same at gaps 10/13/14. The disjoint families (row_major
at 1+1) stay perfectly clean below 8. So overlap alone, at low generator
counts, produces sporadic small errors that the gap>=8 mechanism does not
explain. Do not fold the two together until one of them has a cause.

**Scope of the damage to published numbers:** gap 0..7 is clean, including the
4+4 concurrent case, so bandwidth at those gaps is trustworthy. Every gap >= 8
point in any concurrent sweep is measuring a broken configuration and must not
be quoted.

## PUMICE-038 — the reader's ADDR_HASH compare is inert in the char sim build
**Status:** open 2026-09-14  **Priority:** P1 — it makes any data_mode=1 sim check decorative

Found while implementing [[PUMICE-037]]'s sim repro. In
`ddr2_char_macro_tb_top`, a read engine programmed with `data_mode=1`
(ADDR_HASH) never reports a mismatch:

| mutation | expected | observed |
|---|---|---|
| reader given a hash seed XORed with 0xFFFFFFFF | every beat mismatches | `beats_mismatched=0`, PASS |
| reader pointed at a page nobody ever wrote | every beat mismatches | `beats_mismatched=0`, PASS |
| same two mutations with `data_mode=0` (LFSR) | fail | **fail**, "reader 0 data error" |

So the compare path itself works; it is the hash mode that is inert here.

**Not a board problem.** The board runs `data_mode=1` and DOES report
mismatches — thousands of them, which is how PUMICE-037 was found — so the
RTL's hash compare works on silicon. Something between the CSR write and the
reader's expected-data mux differs in this sim build. `reader_status` shows
`crc_valid=False` at done, and the RTL sets `o_actual_crc_valid <= !r_data_mode`,
so `data_mode` itself IS reaching the engine. Suspect the HASH_SEED0/1/2 CSR
writes: if they are dropped, both sides fall back to the same constant and a
"wrong" seed changes nothing — though that alone would not explain the
unwritten-page case, so measure before believing it.

**Why P1.** Every sim check written in ADDR_HASH mode is currently
decorative, and nobody would know: it passes. This is the CONV-002 shape
(a test that reports green because nothing reads the verdict) in a different
dress. Until it is fixed, sim data checks must use LFSR mode, which is
mutation-verified to fail.

**Do:** program a reader in data_mode=1, read back AXI_ATTR and HASH_SEED0/1/2
over APB and confirm what actually landed; then trace `w_cp_expected` against
`fub_rdata` on a single beat in waves. Both are cheap.

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

