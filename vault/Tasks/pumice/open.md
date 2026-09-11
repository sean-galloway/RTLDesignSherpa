<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

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

| AxLEN | predicted MB/s | measured MB/s |
|---|---|---|
| 1 | 96.1 | 96.2 |
| 2 | 184.6 | 188.1 |
| 4 | 369.2 | 359.9 |
| 8 | 570.0 | 570.5 |
| 16 | 570.0 | 570.7 |

Five points inside 2%, board-measured with `bin/axlen_sweep.py`.

**Two things this rules out.** It is NOT a scheduling bug, and specifically it
is NOT "the read cannot be scheduled until the write is consumed on AXI" (a
reasonable guess, checked and discarded): the characterization runs a write
phase to completion and THEN a read phase, so no writes are in flight while the
reads are measured. It is also not the return ring -- the shortfall did not move
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
2. **Two writers is unsafe in the char harness** ([[PUMICE-027]]). pumice
   returns B out of AW order across masters; the generated write bridge routes
   by FIFO position. Single-writer results are fine. Do not "fix" the bridge
   without deciding whether pumice should guarantee AW-ordered B instead.
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

## PUMICE-027 — write responses leave pumice out of AW order; the char write bridge routes B by position
**Status:** open 2026-09-10  **Priority:** P2
**Found by:** `test_ddr2_char_macro[bank_parallel]` (the only multi-writer scenario), once the
macro suite could compile again (the `-Wno-PINMISSING` waiver for the bridge regen's
`unmapped_*` ports). Fails identically on HEAD's inline macro and on the extracted
`char_engine_block`, so it predates the refactor.

**Symptom:** `pumice_wr_adapter.sv:168` BRIDGE-010 `$error` at ~31 us: "slave returned B out of
AW order".

**Be precise about where the gap is — the per-generator B handling IS built and
is correct.** `bridge_ddr2_char_wr_xbar.sv:222-224,413-415` steers B to the
owning master by `bid_bridge_id` and gates each master's `bready` so only the
owner's ready reaches the slave; the master-side adapters pass their own B
through. That is exactly the queued-B, per-generator-ready design, and none of
it is the problem.

The problem is the **KEY the ownership lookup indexes on**. `pumice_wr_adapter.sv:99-129`
pushes the issuing master's `bridge_id` into `wr_fifo` at AW accept and reads it
at the HEAD: `bid_bridge_id = wr_fifo[rd_ptr]`. So "who owns this B" resolves to
"whoever issued the OLDEST outstanding AW", not "whoever issued the AW whose ID
this B carries". When pumice returns B out of AW order the head names the wrong
generator, and then the otherwise-correct per-master handshake completes cleanly
against it. The steering works; it is aimed by position.

Worth noting for the fix: the adapter ALREADY records the AWID per slot
(`wr_id_fifo`, :156) — but only inside `ifndef SYNTHESIS`, purely to drive this
assertion. The information needed to route by ID is being captured in
simulation and thrown away in synthesis. Routing by ID means searching the FIFO
for the matching entry instead of taking the head, i.e. a small CAM over
`WR_FIFO_DEPTH`. pumice's write CAM commits in FR-FCFS order (oldest schedulable per row, not
global AW order), so with two writers interleaving, a younger writer's B can come back before an
older one's. The check is sim-only (`translate_off`); on the board the B would silently reach the
WRONG generator (its bresp/count is credited to the other gen). AXI4 permits the slave's
reordering between IDs, so this is a system contract gap, not a protocol violation.

**Not affecting the numbers taken so far:** every board characterization run drives generator 0
alone (one writer, one reader), where position routing cannot misroute. Only bank_parallel /
multi-generator runs are exposed.

**Fix options (decide, do not patch blind):**
1. pumice: return B in AW order -- the write-side twin of `pumice_rd_return_ring` (the read
   path already holds R returns to AR order). Costs a small ticket ring; keeps the bridge
   position-routed as generated.
2. bridge: regenerate `bridge_ddr2_char_wr` with ID-based B routing (each generator already
   owns a distinct AWID space in bank_parallel). The converters/bridge family is in-order by
   design, so this is a generator feature.
3. Test-only: run bank_parallel with `SCHED_POLICY.order_mode=1` (in_order) -- confirms the
   mechanism, does not fix the board exposure.

Of the three, (2) is the smallest change and matches what the crossbar already
wants to do: the per-master steering and ready gating stay exactly as they are,
only the lookup changes from "head of the FIFO" to "the entry whose AWID equals
this BID". Option (1) is the bigger statement -- it would make pumice's write
responses AW-ordered like its reads, which is a controller guarantee rather
than a harness fix and would suit any position-routed interconnect downstream.

Also note the BRIDGE-010 message prints the ID strings garbled (`%0h` applied to the message
continuation) -- cosmetic, in the generated adapter template.

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

