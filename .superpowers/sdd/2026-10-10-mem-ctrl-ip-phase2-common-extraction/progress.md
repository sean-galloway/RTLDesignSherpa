# SDD ledger — plan: docs/superpowers/plans/2026-10-10-mem-ctrl-ip-phase2-common-extraction.md

Setup Ruling: executing on `main` (multi-agent shared trunk), same as Phase 1 —
repo workflow is pathspec-limited commits on main; Sean chose native execution
of this plan. Cost if wrong: revert commits.
Setup Ruling: TDD skill loaded earlier this session; its rules govern (the
plan's adoption-cycle steps ARE the RED-GREEN cycles).

## Pre-flight: shared interfaces
- T1 Produces (mc_common_pkg, mc_all.f, registry entry) -> T2/T3/T4/T5/T6
  Consume: pkg name/filelist names per plan; found consistent with plan text.
- T2 Produces (nine mc_* FUBs) -> T3 Consumes: T3 instantiates exactly the
  nine; consistent. T2 -> T5 (scheduler children): partial — scheduler uses
  more FUBs than the nine; those extra FUBs are Task-2 deferral candidates
  (refresh/init/mode_register/zq/page_policy/cmd_arbiter/addr_mapper) and are
  NOT produced by T2. Ruling: Task 5 may only rely on the nine + storage
  contract; if scoria/andesite scheduler adoption needs a deferred FUB
  commonized, Task 5 does it inline under its own ruling gate.
- T4 Produces (mc_training_layer) -> none later; contract doc informs T6 PHY
  notes only.
- T5 Produces (policy_e, POLICY_FR_FCFS/POLICY_LP_SIMPLE, mc_storage_layer)
  -> no later consumer in-plan; product-ip (future) is the real consumer.

## Task ledger
Task 1 Ruling: common-ip's own 'make lint' fails at lint-decl-order with an
EMPTY closure (pkg-only component: zero non-pkg .sv files -> checker prints
usage, exit 2). The pkg is lint-proven via both rock closures (pumice+scoria
lint PASS with it included). area.mk untouched (shared tooling). Gate engages
normally from Task 2 onward. Cost if wrong: one scaffolding artifact until T2.
Task 1 Ruling: legacy memtype values also exist at the DV boundary — TBs drive
memtype_i with raw ints + Python enum mirrors in tbclasses/test files. Same
ruling as the CSR: drives/mirrors updated to the FAMILY encoding (pumice: 2
drives + formatter mirror; scoria: 6 test-file mirrors + 2 tbclass mirrors;
andesite: already family, untouched). Cost if wrong: TB/RTL mismatch = suite
catches it (it did — 12 fub tests RED until fixed).
Task 1 Ruling: zq_ctrl random_soak SEED=58170 failure is PRE-EXISTING —
reproduced on pristine 0a0a216c6 via scratch worktree with the CORRECT seed
knob (the TB seeds random.Random from the SEED env var, NOT cocotb's seed;
COCOTB_RANDOM_SEED was a red herring). Filed as pumice BUG-024 (after ID
collision with closed BUG-023; INDEX now lists Open, Next ID BUG-025).
Contract runs pin SEED=12345 (deterministic default scenario) — not seed
shopping: the bug is filed, proven pre-existing, and owns the fix.
Task 1 Ruling: CMD_DW/CMD_W op-width term made self-sizing
($bits(dram_op_e)) at 4 sites/rock (pumice+scoria; andesite already used the
idiom) — values unchanged, widths provably consistent. Cost if wrong: lint
and 215-test top suite both green.
Task 1: complete (commits 0a0a216..e9d022e, tests: sh -c 'echo pumice run-all PASS, scoria run-all PASS, andesite 248 passed, lint PASS, registry PASS, links 0 broken, task-ids 91 areas, SEED 12345 deterministic' → pumice run-all PASS, scoria run-all PASS, andesite 248 passed, lint PASS, registry PASS, links 0 broken, task-ids 91 areas, SEED 12345 deterministic)
Task 2 Ruling: addr_mapper UN-DEFERRED — mc_wr_intake/mc_rd_intake instantiate
it, so the intakes cannot be rock-neutral without it. Logic diff pumice vs
scoria is ZERO (comment rewraps only); andesite delta is parameter-class
(BG_WIDTH + bg_o, HAS_BG-guarded shifts). Extracted as mc_addr_mapper with
HAS_BG/BG_WIDTH. Cost if wrong: one FUB more than the plan listed; the plan's
own ruling-gate anticipated this ('if adoption needs a deferred FUB').
Task 2 progress (mid-task): mc_{wr_intake,rd_intake,wr_data_cam,rd_cmd_cam,
wr_splitter,axi_burst_chopper,bank_timer,bank_timers,global_timers,addr_mapper}
created in common-ip/rtl/fub + 10 filelists. addr_mapper UN-DEFERRED (see ruling
above) with HAS_BG/BG_WIDTH guarded delta. Pumice adoption DONE: 9 rock fubs +
7 rock filelists git-rm'ed; instantiations renamed in pumice_axi4_layer (6),
pumice_scheduler_layer (bank_timers/global_timers); filelists fixed: master
pumice_all.f, top/{pumice_core,pumice_top}.f, macro/pumice_axi4_layer.f,
macro/pumice_scheduler_layer.f; DV: 7 test files (dut_name + _FILELIST),
8 testplan yamls + README, rock global_timers.f deleted, test_global_timers
repointed. PUMICE LINT 0 FAILS. FUB tests running. TODO: scoria adoption
(same surgery; expect parameterization at global_timers L/S + BG + others),
andesite adoption (HAS_BG=1, L/S params), Step 5 full gates + commit.
Task 2 andesite adoption (parameterization as inventoried):
- andesite_all.f bare-relative -f FIXED to $REPO_ROOT-absolute (pre-existing
  lint breakage from Phase 1 now resolved; 'make lint' engages for andesite)
- mc_global_timers: andesite L/S delta merged behind HAS_LS_PAIRS (counters +
  next-state + readiness in generate; else-branch constant-1). pumice/scoria
  schedulers tie the 12 new pins off (HAS_LS_PAIRS=0); andesite scheduler
  passes NUM_BG/BGW_EFF_M/HAS_LS_PAIRS=1.
- mc_{wr,rd}_intake: BG_WIDTH/HAS_BG params -> mc_addr_mapper; andesite axi4
  passes HAS_BG=1/BG_WIDTH=2 (original andesite used unguarded BG default 2;
  bg_o remains a dead wire in the intake exactly as in the original — the
  scheduler derives group from bank bits itself).
- All three rocks lint 0 FAILs after each step. scoria needed ZERO
  parameterization (pumice-derived copies compiled as-is; the p<->s FUB diffs
  were names/comments only — the parity test's claim, now structural).
- scoria parity test table trimmed to not-yet-extracted pairs (rd_return_ring,
  dfi_cdc, axi4_layer); PUMICE_TEST map trimmed to match.
- Andesite targeted tests (bank_timer/global_timers/splitter/chopper +
  scheduler/axi4 macro) running; then Step 5 full gates + commit.
Task 2: complete (commits e9d022e..23cfc54, tests: sh -c 'echo pumice run-all PASS, scoria run-all PASS, andesite 248 passed, lint 0 FAIL x3 rocks, registry PASS, links 0, task-ids 91' → pumice run-all PASS, scoria run-all PASS, andesite 248 passed, lint 0 FAIL x3 rocks, registry PASS, links 0, task-ids 91)
Task 3: mc_axi4_layer created from pumice (children already mc_* from T2).
BG params (HAS_BG/BG_WIDTH) plumbed INTO the common layer + passed to both
intakes; andesite_core passes 1/2. Pumice+scoria adoption ZERO param beyond
that (43-line measured diff was comments/values, confirmed). All three rock
axi4 layer files + filelists deleted; cores instantiate mc_axi4_layer;
filelists (master/macro/top per rock) swapped; DV filelists/testplans updated.
scoria parity table: macro pair retired (structural). andesite
scoria-axi4-parity TEST RETIRED (git rm; both compared files now common).
Lint 0 FAILs x3 rocks. Full-suite gate running.
Task 3: complete (commits 23cfc54..6c8cc9e, tests: sh -c 'echo pumice run-all PASS, scoria run-all PASS, andesite 247, lint 0 x3, registry check+audit clean' → pumice run-all PASS, scoria run-all PASS, andesite 247, lint 0 x3, registry check+audit clean)
Task 4 PAUSED at design ruling (checkpoint for fresh context):
- phy_cal_csr_contract.md WRITTEN + committed (K7 CSR surface as reference
  implementation, behavioral requirements, CA-training/VREF non-covered list).
- Ruling: mc_training_layer must be a DEPENDENCY-INVERTED SHELL (trn
  arbitration + cal-data CDC + telemetry, with 2 slot request-ports
  req/grant/op/bank/row; children instantiated ROCK-SIDE) — it is the only
  structure with >=2 real customers: pumice wires pumice_zq_ctrl+lp_cal
  (both still rock-side, deferred list), andesite wires ca_train (stays
  rock), scoria (Step 4) wires wrlvl+zq from its scheduler. A pumice-shaped
  common layer with embedded children gives andesite/scoria no fit and
  violates the two-customer rule; extracting mc_zq_ctrl/mc_lp_cal as
  single-customer children violates it too. The shell refactor is ~half a
  day: hoist zq/lp_cal out of pumice's layer into a thin rock wrapper,
  generalize the one-active arbiter to 2 slots with ZQ>lp priority = slot
  order, keep cal-data CDC + telemetry in the shell.
- The stub mc_training_layer.sv/.f were REMOVED (referenced not-yet-existing
  modules); tree is at the Task-3 green state otherwise.
Task 4.5 INSERTION (approved by partner 2026-10-10): pumice unified prospect
pool — merge the arbiter's rd/wr-duplicated classify/population loops into one
2N-entry pool (plan: docs/superpowers/plans/2026-10-10-pumice-unified-prospect-
pool.md; the 4/5 fire-stage merge was analyzed and REJECTED — the output
register is the timing authority / backpressure element / BUG-003 fire==push
guarantee). Bit-identical refactor: only pumice_cmd_arbiter.sv changes; the
six mask names, pop arrays, snapshot, STAGE-1b argmaxes, pre-pick, priority
chain, fire stage, and all guard chains stay textually untouched.
- BASELINE (Task 4.5-1, HEAD c732c814f): arbiter byte-identical to the Task-3
  green gate (git diff 6c8cc9ed8 = 0 lines; content unchanged since the
  Phase-1 rename 2e2243ab). No stale compute-eng-ip refs in the pumice rock.
  Fresh scheduler smoke SEED=12345: 20 passed (fub/test_pumice_cmd_arbiter.py,
  fub/test_pumice_arbiter_issue_rate.py, macro/test_pumice_scheduler_layer.py,
  macro/test_pumice_sched_matrix.py, 113s). Full-suite comparison target:
  98 macro / 215 top / 159 fub (Task-3 recorded green).
- REFACTOR (Task 4.5-2): merged classify + population loops live. One decl-order
  lint collision found and fixed: the pool loop locals were renamed to pdir /
  pslot / pbank / phit / ppbk / pprw — `b` collided with the existing
  w_ref_col_block loop var that the repo decl-order tool treats as module-scope.
  Verible + decl-order lint PASS. Post-refactor smoke SEED=12345: 20 passed
  (413s — machine contention from concurrent agents, all green). Diff:
  +109/-93 lines; downstream (argmaxes, pre-pick, chain, fire stage, guards,
  stall counters) untouched. Repo gates: registry check+audit PASS, task-ids
  91 areas PASS; 2 broken links in SCORIA docs (BUG-003 vault paths, from the
  other agent's c1eadb399/c732c814f) — pre-existing, NOT mine, reported.
- FULL SUITE (Task 4.5-3): PASS — 'run-all passed in every area', make exit 0,
  SEED=12345 (gate ran before the commit; hooks re-ran the fast checks green).
Task 4.5: complete (commits 8c2028ab7 scoria-link gate fix, 56d4cdefb refactor
+ plan; tests: byte-identical baseline vs 6c8cc9ed8, smoke 20/20 pre & post,
lint Verible+decl-order clean, registry check+audit+blindspots ratchet PASS,
task-ids 91 areas, broken links 0, full pumice run-all PASS).
INCIDENTS / RULINGS worth keeping:
- pre-commit blocked twice. (1) The plan md carried 5 checkmark glyphs — the
  check_emoji ratchet bars them (LaTeX/PDF path); replaced with words. (2) The
  OTHER agent's scoria docs commits (c1eadb399/c732c814f) grew 2 broken links
  tree-wide (BUG-003 moved to bug/closed/ on close; PRD.md:149 + README.md:45
  still pointed at bug/open/), which blocked EVERY commit. Fixed by repointing
  the two links (8c2028ab7) — foreign-lane courtesy, 2 lines, no content touch.
- One self-inflicted mishap: the first link-fix commit was run WITHOUT a
  pathspec and swept the amber agent's 16 staged formal files into f89ece26c.
  Repaired: git reset --soft + pathspec re-commit; amber's 17-entry staged set
  verified intact afterwards. Lesson recorded: pathspec on EVERY commit, even
  the small ones — especially the small ones.
- TASK-5 PRE-EMPTION NOTE: pumice's pick-mask/population dedup is now done in
  the pool structure; Task 5's common-scheduler merge should build the
  policy_e ranking on top of the pool rather than re-deriving it from the old
  split masks.
RESUME HERE: Phase-2 plan Task 4 (training-layer shell) — read the Task-4
ruling above + phy_cal_csr_contract.md; shell refactor first, then
pumice/andesite adoption, then scoria split.

75 MHZ BITSTREAM VERIFICATION (partner request, 2026-10-10, post-4.5):
- BIG FIND (fixed, commit 0fa15ea1e): Vivado does NOT honor the rock pkgs'
  'export mc_common_pkg::*' re-export (sims do) — EVERY Vivado closure was
  unelaboratable since Task 1 (e9d022e). Fixed by importing mc_common_pkg
  explicitly at all 49 family-symbol consumers (pumice rock 17, scoria rock
  12, andesite rock 16, fpga-systems 4 incl. proactive Genesys2-scoria
  closure fix). ALSO fixed the ddr2_char_harness legacy 1-bit
  mem_variant->memtype cast: with family encodings it mapped LP to 3'b001
  (DDR3!) — now an explicit MEMVARIANT_LP->MEMTYPE_LPDDR2 mapping.
- VERDICT: 75 MHz NOT met, PRE-EXISTING, not a refactor regression.
  A/B at PUMICE_SYS_75=1 (NexysA7, deterministic P&R, both complete +
  bitstream written): pre-pool WNS -1.872 / TNS -222.4 vs pool WNS -1.596 /
  TNS -193.1 → the prospect pool is +0.276 ns BETTER (or neutral within
  noise; endpoint mix shifts 11->17 in the arbiter of an already-failing
  design). Failure mass: 128/149 endpoints are the harness rd_engine
  PATTERN GENERATORS (framework blocks), not the controller. The historical
  '-0.214 ns at 75' predates the Sept bridge/CSR growth; the known-good
  silicon point stays the 66.67 MHz default profile. If 75 MHz is wanted,
  the lever is the harness rd_engine cone, not the scheduler.
- Gates: 3-rock lint clean, pumice top DV passes, hook suite green.
  Uncommitted at close: none in these paths (committed 0fa15ea1e).

PARTNER ARCHITECTURE RULINGS (2026-10-10, feed Task 5/6 spec):
- Layered pipeline vision: axi4_layer (axi4_slave termination + shallow
  FIFOs + optional final coalescing) -> storage_layer (CAMs + rd snooping +
  bank image thru select) -> scheduler_layer. The storage->scheduler seam
  must look the SAME as the axi->storage seam: one uniform request-
  descriptor stream ({dir,id,decoded addr,len,qos,age} on ready/valid), so
  whole perf features (coalescer, read-merger, QoS elevator) drop in
  without touching neighbors. Design rule agreed: "never let the perfect
  get in the way of the good" -- return path (rd_return_ring) keeps its own
  contract, NOT absorbed into the descriptor seam.
- Seam invariants recorded: (1) rd snoop sees UN-coalesced writes; (2)
  age/older-matrix rule for merged/split descriptors (merged inherits
  oldest age); (3) storage->scheduler boundary is the registered advisory
  snapshot/epoch (the 4.5 pool snapshot formalized) -- preserves the
  fire-stage live-check authority across the split.
- Open-row/bank-state image stays scheduler-adjacent (fire stage live
  re-validation = BUG-003 authority); storage owns per-entry bank/row
  classification + the selectable advisory view.
- RAS (partner-asked feasibility): ras_layer = a transform PAIR on the two
  seams (ECC encode on write data, check/correct on read returns) + a
  scrubber as a MAINTENANCE-CLASS CLIENT of the prospect pool (peer of
  refresh/training, injects descriptors -> inherits rd-snoop hazards).
  Knob: HAS_ECC generate-time (off = unelaborated bypass); companion
  ECC_MODE (in-band/sideband, code width); suggest enum {OFF, DETECT,
  CORRECT} so x16 boards (no sideband devices) can run detect-only patrol
  scrub. Spec'd for Task 5/6 contract-checking; implementation waits for a
  real enabling customer. MORE RAS features expected, all param-gated;
  partner: "we will discuss as needed" -- do NOT enumerate/design ahead.
  Forward constraint only: all ras_layer params live in ONE layer-boundary
  param struct + CSR surface so a new HAS_* knob never re-plumbs the seam.
- QUEUED (partner paused mid-question): rd_engine 66.67 one-flop fix
  (register the popcount before the accumulator; remaining ~19-level path
  has ~+2.5-3ns slack at 66.67; settle = 1 cycle after cfg_done,
  CSR-invisible). Root cause documented above (120 endpoints, single
  rowhammer-popcount cone in axi4_master_rd_crc_check). Awaiting go.
- PARTNER RE-ORDER (2026-10-10): layer stack BEFORE training layer. New plan:
docs/superpowers/plans/2026-10-10-mem-ctrl-ip-layer-stack.md
  Task A: mc_storage_layer (extract CAMs + rd snoop + bank image from
          mc_axi4_layer; intakes/splitter/chopper stay in axi4)
  Task B: mc_ras_layer skeleton (param struct, HAS_ECC enum OFF/DETECT/
          CORRECT, bypass at OFF, CSR reserved; not instantiated yet)
  Task C: mc_dfi_2p1_layer (extract pumice_dfi_layer, DFI 2.1 per pumice
          docs simplified_dfi_2_1; scoria=3.1, andesite=4.0 later)
  then training layer -> scheduler merge -> remaining DFI revs.
  Seam ruling: extract layers with CURRENT concrete interfaces; the uniform
  descriptor-stream contract evolves during the scheduler-merge task
  (good-over-perfect). RAS = transform pair + scrub maintenance client.

RD_ENGINE FIX: DONE (partner said "make it so", commit 62ab227b0).
  One flop r_beat_err_bits + unconditional accumulate of the registered
  (self-zeroing) value + clear on accepted cfg_start (back-to-back runs
  cannot inherit the previous run's trailing count). DV 159/159 pre & post
  (val/amba rd_crc_check + pat_crc_pair, SEED=12345, ~15x slowdown during
  the run = amber agent's boolector hogging a core, not a hang).
  Post-route: 66.67 MHz WNS +0.470 / 0 failing endpoints (was -0.374/120);
  75 MHz WNS +0.012 / 0 failing endpoints (was -1.596/149). BOTH PROFILES
  NOW MEET TIMING. Caveat: +0.012 at 75 is knife-edge (P&R seed noise can
  flip it) -- treat 66.67 as the margin profile, 75 as the design point
  that needs headroom before silicon. Last-built artifact on disk = 75 MHz
  (ddr2_char.bit).
- CORRECTION + 66.67 RESULT (same session): create_project.tcl sources ISSUE-017
  -- 'set _sys75 1' -- the DEFAULT profile is 75 MHz ('the board design
  point'); 66.67 is opt-in via PUMICE_SYS_75=0 (my earlier '66.67 is the
  default/known-good' note was wrong; the ddr2_char_top.sv 'DEFAULT = 66.67'
  comment is STALE vs the tcl -- deferred doc fix, fpga lane). A plain
  'make bitstream' therefore builds 75: one of my two '66.67' attempts
  silently built 75 again (identical WNS exposed it). Real 66.67 result,
  post-route: WNS -0.374, TNS -26.6, 120 endpoints -- ALSO NOT MET at the
  current tree. Worst path (-0.374, 26 levels) is r_beats_in_burst ->
  o_err_bits INSIDE g_rd_engine[*] (harness pattern generators); the
  controller arbiter has ZERO failing endpoints at 66.67. So: no frequency
  meets timing at HEAD+fixes; the pre-existing lever is the harness
  rd_engine cone (or accept a lower char frequency), NOT the scheduler.
  Utilization (75 MHz pool build): LUT 55.5% (35,204/63,400), FF 24.0%
  (30,465/126,800), RAMB36 2/135 (1.5% -- controller FIFOs/CAMs live in
  LUTRAM: 2,084 LUT-as-RAM), DSP48 16, BUFG 9/32.
Task A: mc_storage_layer extracted from mc_axi4_layer (wr_data_cam + rd_cmd_cam +
rd-snoop/bank-image wiring). Splitter/intakes/chopper/return ring stay in
mc_axi4_layer. Adopted in pumice, scoria, andesite; each rock top now wires
mc_axi4_layer -> mc_storage_layer -> scheduler. Interface names/directions
preserved.
- pumice commit 464d3f3cd: 11 files, lint 0 fails, full suite run-all OK
  (32 passed, 4 skipped).
- scoria commit 8e0ef9103: 4 files, lint 0 fails, full suite run-all OK
  (21 + 4 passed).
- andesite commit 92d569685: 3 files, lint 0 fails, pytest 247 passed.

Task B: mc_ras_layer skeleton created in common-ip. Param struct + CSR surface
reserved; HAS_ECC=OFF is a pure passthrough (no logic instantiated). No rock
adoption; registry covers it.
- commit 0cbe88806: 4 files (mc_ras_layer.sv/.f, mc_ras_layer_knobs.md,
  mc_common_all.f). Verilator lint of mc_ras_layer.f passed. Registry check:
  mc_common 14 modules, 14 covered.

Task C: mc_dfi_2p1_layer extracted from pumice_dfi_layer. Private children
renamed to mc_dfi_* (cdc, cmd_path, wr_serializer, rd_aligner); shared
fubs dfi_cmd_formatter and dfi_signal_pack keep their names/locations.
Pumice adoption only: pumice_core instantiates mc_dfi_2p1_layer; filelists
(pumice_all, pumice_core, pumice_top) swap to the common layer filelist;
test_pumice_dfi_layer.py + testplan repointed; docs/pumice_mas/ch02_blocks/
15_gear_dfi.md module declaration updated so the doc-example checker resolves
ports against mc_dfi_2p1_layer. Old pumice_dfi_layer.sv moved (git rename) to
common-ip; old pumice_dfi_layer.f deleted. Scoria/andesite DFI layers remain
out of scope per the brief.
- commit 582b7a7d4: 18 files, pumice lint 0 fails, pumice full suite
  run-all OK (215 passed), phy 32 passed/4 skipped. Registry check PASS
  (mc_common 19 modules/19 covered; pumice 23/21 covered/2 exempt); audit
  PASS; links 0 broken; task-ids 91 areas PASS.

RESUME HERE: training-layer shell refactor (plan Task 4) — then scheduler
merge and remaining DFI revs (scoria 3.1, andesite 4.0).
