# SDD ledger — plan: docs/superpowers/plans/2026-10-07-amber-rtl-completion.md

## Controller rulings (pre-flight, 2026-10-07)
- R-D11-ARRAYS: keep the landed per-way tag/data arrays; `sdpram_core` the
  module is an AXI burst slave (wrong shape for same-cycle multi-way tag
  compare). D11 satisfied via house primitives: gaxi_fifo_sync queues
  (D-6) + genuine sdpram_core consumer = pair-rig shared memory (Task 11).
  MAS ch01/ch03 contradiction errata'd in Task 14.
- R-D9-RANDOM: approve the recorded cache_sim LFSR-extension for RANDOM
  parity (exact native parity for LRU/FIFO); symmetric to PRD D7's
  documented tree-PLRU no-golden caveat.
- R-MAS-ERRATA: landed `amber_snoop_resp` binding port names are binding
  over MAS ch02 spelling; full MAS errata queue folded into Task 14.
- R-PAIR-SIDEBAND: approve the `coh_req_{valid,addr,type}` coherence
  sideband + amber_pair_fabric for the pair rig (D10 gated deliverable
  cannot express upgrades on plain AXI4); onyx proper waits per D10.
- R-WORKFLOW: shared main, pathspec commits, per-task implementer+reviewer
  (kestrel pattern). PRD D3/D11 closed as v0.6 in the same commit as the
  plan.

## Progress
- Setup: plan + PRD v0.6 committed; workspace created.
- Task 1: complete (commits ade6638a9..002554796, review approved; minor:
  amber_all.f flattens amber_pkg.f 11x - watch for duplicate-package errors
  in lint flows; unit TBs use per-block lists so sims unaffected)
- Task 2: complete (commit 8b87f3917): pkg control-plane enums
  (ctrl_state_t + D-3 INIT, AMBER_EV_* MonBus codes, amber_ace_req_t,
  amber_miss_class_t, all additive) + gem5-derived FSM oracle
  (dv/golden/amber_fsm_oracle.py, 10 states = MESI + 6 D-11-collapsed TBE
  transients, 103-row cited table, pkg pinned via amber_snoop_kmap sim).
  Divergences from gem5 directory semantics recorded in
  dv/golden/gem5_mapping_notes.md §4 (IHI0022/pkg Table 3.0 wins).
  run-all-func 165 passed (38 baseline + 127 new).
- Task 2: complete (commits 002554796..726994dda; 103-row gem5-cited oracle,
  8 recorded divergences, pkg pinned via live sim; fix round 1 closed citation
  defects C1/I1 + minors, re-review clean; T3 carries: pin _im_step
  pending-clear corner, M_I as scoreboard initial-condition)
- WATCH: foreign lane's error_injector.sv lost from worktree; recoverable via
  git diff 8b87f3917 4f9898bb6 -- projects/components/utility-ip/misc/rtl/
  error_injector.sv (dangling commits 4f9898bb6/a489203d7) - owner informed
- Task 3: complete (commits 726994dda..dafb853cd, review approved 0 C/I;
  control FSM oracle-lockstep green both geometries ~664k checks)
  minors carried: (1) T4 decides whether CLEAN_UNIQUE upgrades arm pf per
  MAS ch02/02; (2) be==0 / stray req in INIT / mid-txn reset unstimulated -
  list in T4+ testplans; (3) record RDS_SEED_BASE in reports for replay;
  (4) fill stub's one protocol fact (CLEAN_UNIQUE=no beats) is pinned, safe
- Task 4: complete (commits 42016dfd7 + 9da9b1546 completion round: fresh-seed FULL matrix green both geometries under RDS_SEED_BASE=20261007-t4-completion-731924, S-ref polarity + IDLE-grant directed, _hit_way model fix) — pending-fill bypass leaf + CTRL_SNOOP service;
  pf-arming decision: upgrades do NOT arm the bypass (MAS ch02/02, no fill data
  in flight; pinned by UpgradeNoBypassArm); _im_step pending-clear corner CLOSED
  IN ORACLE (invalidation-sticks, pinned by ImStepPendingClearCorner + 5 new
  oracle rows); kmap pending_bypass_match axis driven on the snoop path, verdict
  recorded; MINOR-2: be0 + stray-in-INIT implemented, mid-txn reset recorded
  not_implemented (Task 9/14); snoop classes a-d all directed + idle soak
- Task 4: complete (commits dafb853cd..9da9b1546, 2 rounds; fresh-seed FULL
  matrix green both geometries ~687k checks; snoop-during-fill verified;
  3 soak-found bugs all TB-model-side, DUT correct each time; S-ref polarity
  + IDLE-grant directed tests added; T5+ must keep the FULL soak in regression)
- Task 5: complete (commits 6d8227161 + 610ea3bab): amber_victim depth-1
  leaf (MAS ch02/05 fields + victim_clear retire + load-while-busy ignore)
  instantiated in amber_control; CTRL_SNOOP ref resolution gains the
  buffer-side bypass term (victim_valid && line match -> M, CD sourced from
  victim_data; tag-array sn_victim_gnt deleted); D-5 gather-complete strobe
  phrasing recorded (final-beat-registered cycle, not comb on the read);
  TB: EVERY-CYCLE victim invariant + VictimBufferHandshake +
  SnoopHitsVictimBypass (array-poison source discrimination, bd_wr tagging)
  + SnoopPriorityDuringGather (samples= grant-window analysis); new
  dv/testplans/amber_victim_testplan.yaml; gate/func green both geoms
  (596/7223/1893/11497 checks), func baseline 174 passed, FULL soak under
  RDS_SEED_BASE=20261007-t5-224621 (s016w2 seed 79156: 1,167,246 checks /
  s128w4 seed 60303: 1,138,140 checks; 0 mismatches both; s128w4 exact
  reproduction verified zero-interference); controller follow-up dropped
  the duplicate amber_victim.f pull from amber_all.f
- Task 5: RTL approved by review (all corners by-construction sound, no
  C findings); sign-off held on FULL-soak evidence — controller's first
  launch failed (wrong make context), re-run launched correctly from
  dv/tests with RDS_SEED_BASE=20261007-t5-224621 (task bash-kudrqptw);
  duplicate amber_victim pull in amber_all.f fixed (610ea3bab);
  minors for later: same-line-snoop-during-gather composition test (T7),
  leaf testplan beat-gating sentence (T14)
- Task 5: SIGN-OFF COMPLETE — FULL soak green from the committed tree under
  the recorded base (6 cells, 25.5 min, /tmp log via task bash-kudrqptw;
  evidence condition from the review closed; log referenced in task-5
  report via this ledger)
- Task 6: committed 9ca3eb02c (fill/drain engines, FULL soak green both
  geometries, baseline 178); review next
- Task 6: complete (610ea3bab..9ca3eb02c, strong approve; DEPTH=4 arithmetic
  verified conservative vs landed control; wrapper contract line-accurate;
  compliance-checker deviation = genuine framework race, sound replacement
  monitor). Integration watch items for T7+: beat-consumer backpressure
  (fill pops unconditionally), fill_beat_idx wrap fragility, RRESP/BRESP
  unacted (T14 deferral)
- Task 7: complete (commit 76dcb2c6d, controller-verified recovery commit
  of the implementer's staged tree; worktree==commit verified): closed loop
  REAL amber_control + landed tag/data/repl + REAL amber_snoop_resp via the
  new harness dv/tb/amber_snoop_resp_th (snoop_resp ctrl_* <-> control
  internal, taps observed; data write port muxed; NEW quiescence-guarded TB
  tag-write backdoor for E seeding). Six pre-existing scenarios stay green
  under the same cell names + NEW real_control_loop (randomized snoops vs
  an amber serving random CPU traffic, both ports live: pending-line /
  dirty-victim buffer / clean-victim stale (live-copy discrimination) /
  other-line targets, post-commit pend mirrored, killed-fill re-fetch
  compositions) + SnoopVictimLineDuringGather composition (T5 minor).
  TWO found-and-fixed amber_control bugs, both invisible to the control
  suite: (1) HIT_WR E->M promotion drove an all-zeros way one-hot (silent
  drop; pinned by new gate scenario EWriteHitPromotes); (2) sn_stale_gnt
  missed the set-equality term (cross-set way+tag collision false-stale;
  caught twice by the loop). Base _score_slice gained a hit-promotion
  branch (inert for control). Evidence: gate/func/full both geoms 0
  mismatches/0 ACE violations (full ~820k checks per cell); recorded
  fresh-seed FULL soak under RDS_SEED_BASE=20261008-t7-041128 (6/6, seeds
  55695/18514/47925/84446/31359/54189, 0 mismatches); amber func baseline
  178 passed first-hand; control suite re-run 4/4 func + 152 gate/func.
  Watch items closed: CD-stall straddling drain_done is safe (amber_victim
  clear drops valid only, payload registers hold); fill-beat port free
  during CTRL_SNOOP confirmed. DV trade-offs recorded in the testplan:
  window-sensitive mid-txn snoops use fast AC+CD (CR keeps level
  backpressure) and order first; mid-txn AC valid_delay up to 50cy would
  otherwise move the grant past the window. Foreign verilog_condensed_lrm.sv
  + coverage_reports left unstaged. FULL report:
  task-7-report.md
- Task 6: complete (9ca3eb02c, strong approve 0 C/I)
- Task 7: committed 76dcb2c6d; implementation STRONG APPROVE (genuine
  concurrent loop, composition scenario, 2 found-and-pinned RTL bugs:
  HIT_WR promotion one-hot dead path :944, sn_stale_gnt set-narrowing :533);
  sign-off CONDITIONAL on FULL soaks (snoop_resp + control re-run, live-path
  fix) — launched bash-cds3rjx6, base 20261008-t7-signoff
  minors deferred to T14: testplan line cites 218->944 / 233->531-535,
  stale stub-era comment tb:109, commit-message framing note
- Task 7: SIGN-OFF COMPLETE — FULL soaks green from committed tree
  (snoop_resp 6/6, control 6/6 @19min, base 20261008-t7-signoff,
  task bash-cds3rjx6); found-and-pinned bugs recorded
- Task 8: instance capped mid-TDD — TBs/testplans/test files WRITTEN,
  RTL (amber_cpu_frontend.sv, amber_monlite.sv) NOT yet written
- Task 8: instance fixed the func mismatch in-worktree (frontend func 4/4
  green on controller re-check); instance completing FULL+monlite+baseline
- RULING (monitor placement, 2026-10-08): generic drop-and-count MonBus
  emitter -> utility-ip/misc (dma_address_gen precedent) as a follow-up
  lift task before jet builds; cache event codes become a cache-ip family
  pkg at lift time; amber keeps tap wiring. T8 must keep the emitter/tap
  boundary clean inside amber_monlite (T8 reviewer: verify the split).
- Task 8: SIGN-OFF — FULL soaks green from committed tree (frontend 6/6
  41.8s, monlite 12/12 47.8s, base 20261008-t8-signoff); whole-area func gate
  re-run first-hand 190/190 from committed tree; commit 46e03987b already on
  origin/main (HEAD==origin/main verified 2026-10-08). PRIMARY-MODEL REVIEW
  STILL OUTSTANDING — dispatch before/with T9; carry the monitor-placement
  ruling (emitter/tap boundary cleanly separable inside amber_monlite).
- Task 8: review round 1 (agent-84, primary) — spec FAIL 1 Important (plan-mandated:
  D14 gaps not carried into amber_cpu_frontend/amber_monlite testplans —
  illegal-ACSOOP + mid-transaction reset absent rather than recorded-deferred;
  testplan-only fix: two carry-forward entries w/ rationale + suite pointers).
  5 minors. RULING (controller): minors 1-2 RATIFIED as documented deviations —
  (1) monbus_tally_axil unconsumed: suite scores the packet stream directly,
  tally parsing is the tally's own burden, tested at system level (T11);
  (2) present-vs-absent substitution: cycle-identical-under-stall +
  USE_MONITOR=0 silence + inherited-suite pass is strictly stronger than the
  literal brief step; structural output-only guarantee covers tap-vs-notap.
  Minors 3-5 to fix round 1: DROP_CODE parameter for emitter-lift cleanliness;
  tap_miss_class constant-tie gap line; remove dead _wait_event helper.
  Reviewer verdict: Needs fixes.
- Task 8: fix round 1/5 (1 Important addressed — D14 carry-forward entries in
  both testplans w/ rationale + suite pointers; minors 3-5 addressed —
  DROP_CODE param makes generic engine literally amber-free, tap_miss_class
  gap line paired, dead _wait_event removed; 0 open; commit 180bf7bc6;
  covering tests monlite gate 4/4, monlite func 8/8, frontend func 4/4)
- Task 8: complete (commits 76dcb2c6d..180bf7bc6, review clean after 1 fix
  round — primary reviewer agent-84: spec FAIL 1 Important plan-mandated D14
  carry-forward lapse + 5 minors; fix round 1 by agent-83 commit 180bf7bc6;
  scoped re-review agent-85: all 4 findings ADDRESSED, no new breakage.
  Controller rulings recorded: minors 1-2 ratified as documented deviations
  (tally deferral, pva substitution). Soaks: frontend FULL 6/6, monlite FULL
  12/12 base 20261008-t8-signoff; func 190/190 pre-fix; emitter/tap boundary
  verified cleanly separable — DROP_CODE param makes generic engine literally
  amber-free for the utility-ip/misc lift.)
- RULING (user directive, 2026-10-08): amber_monlite's MonBus output queue
  becomes a house gaxi_fifo_sync (replaces hand-rolled queue storage);
  drop-and-count / DROP_CODE / USE_MONITOR tie-off semantics preserved;
  strengthens D11 (house shared storage primitives). Cost if wrong: observer
  path perturbation — pinned by the pva cycle-identical suite + gate/func/FULL.
- RULING (user directive, 2026-10-08): amber macro compositions (lookup /
  miss-fill / eviction / coherence groups discussed pre-T9) are NEW SV wrapper
  modules so cocotb drives a real DUT top — not Python-side composition.
  Test-only wrappers take a `_test` suffix (user-approved; repo `_th` idiom
  stays for plain harnesses). Slotted into the T9 brief as a macro-suite
  subtask. Cost if wrong: a few dv/tb files to rename.
- Task 8 (post-review user-directed change): monlite MonBus queue on house
  gaxi_fifo_sync committed 35ca955fb (agent-83); scoped review agent-86:
  Approved — deferral accounting re-derived bit-identical in reachable states,
  no backpressure leak, filelist/TB sound, 195k-check FULL evidence. ONE
  Important: chained-deferral corner defended only by FSM-unreachability claim
  that grant-independent taps (tap_snoop_fire/tap_drain_done) don't fully
  support — fix: budget room on true effective occupancy
  (w_room1 = eff_cnt + r_pend_q <= OUT_DEPTH-1), one line, pin-identical.
  Minors deferred: USE_MONITOR=0 internal drift (unobservable at pins),
  probe count semantics shift (debug-only). Fix round → agent-83.
- Task 8 (post-review user-directed change): COMPLETE — gaxi_fifo_sync MonBus
  queue 35ca955fb + room-budget hardening 39ab8d9d6 (scoped review agent-86
  Approved w/ 1 Important chain-overflow corner; fix round + re-review
  agent-87: ADDRESSED, no new breakage; gate 4/4, func 8/8, FULL 12/12
  unchanged, lint clean). Minors deferred to final review: USE_MONITOR=0
  internal drift (unobservable), probe count semantics (debug-only).
- RULING (controller, 2026-10-08): macro-suite composition work is scheduled
  as Task 9.5 — immediately after T9 core bring-up, before T10 parity grid
  (which consumes the core). T9 stays focused (core smoke + oracle lockstep);
  macros harden interactions in parallel with T10; T11 pair rig inherits the
  pinned macros. Plan file updated with the T9.5 task text. Cost if wrong:
  one plan edit + one extra dispatch.
- Task 9: complete (commits 39ab8d9d6..adde175db + amber_core.f swept into
  foreign 78710cba3 disclosed, review APPROVED agent-89 primary: pure-structural
  verified — zero always_ff in core, D3/D-8 shape signal-level, filelist +
  area registration confirmed, TDD evidence credible, init-walk edge pinned;
  WARN D11-verbatim-in-commit-body closed by controller first-hand — text
  matches mandated ruling word-for-word. 4 minors deferred to final review:
  triple gaxi_fifo_sync.f closure comment, tap_miss_class UNKNOWN testplan
  line, core-grid REPL {FIFO,LRU} only coverage note, USE_MONITOR=0 cell
  absent at core level). 9/9 FULL cells green, 0 mismatches, ~60k checks/cell.
- RULING (controller): plan file updated with the T9.5 macro-suite task text
  (non-Task heading so task-brief awk stays unambiguous).
- Task 9.5: complete (commit 790d76c37, review APPROVED agent-91 primary: four
  correctly-composed _test wrappers, zero existing-file modifications, T7
  promotion verified verbatim-by-inheritance, four hard compositions pinned,
  both T7 bug pins travel, adaptations DV-side/logged/non-weakening.
  WARN zero-gap-mid-miss closed by controller first-hand — report line 159:
  coh tiny FULL 876,481 checks / 7,342 snoops incl. zero-gap AC pairs at the
  geometry T7 never ran. 5 minors deferred to final review: runner boilerplate
  dup, adaptation-1 pool-desync risk, dead runner locals, lookup soak trivial
  redundancy, _WriteThroughMem byte-dup across two TBs). Area 212 cells green.
- Task 10: complete (commit b8c45bea6, review APPROVED agent-93 primary:
  grid shape verified, exact-count strict != with non-vacuity selfcheck,
  gen_traces --check re-verified by reviewer, extension anchored once-exactly
  vs shipped model.js with lockstep callouts in both files vs rtl/fub/amber_repl.sv
  seed/taps, runner validation ordered pre-sim, named risks 1-3 all clean.
  WARN x2 closed by controller: fail-first log is ephemeral by nature — the
  catching lockstep is permanent in every sim cell + 48/48 verified; seed
  pinning matches landed house convention. 3 minors deferred: epoch-pin
  durability (implicit pin adequate), decorative RANDOM seed arg, inverted
  mismatch-condition readability). Area 260/260.
- Task 11: complete (GATED DELIVERABLE — commit a7cf72ed8, review APPROVED
  agent-95 primary: fabric flow/PassDirty absorption+AR suppression/RR/depth-1
  CD buffer verified in-diff, scenarios a-g real, lockstep extends Task 2
  oracle with grant-observed resolution (fabric misresolution cannot hide),
  all 5 soak-found fixes verified genuine strict-checked RTL fixes w/ recorded
  rationale, sdpram = D11 genuine consumer, MAS port list modulo disclosed
  errata. 8/8 FULL @20261009-t11-signoff, area 266/266 twice. 5 minors
  deferred to final review: vacuous grants-len check in (e), testplan
  overstates (g) nomon coverage (gate-only), dead var in (b), build-dir
  race follow-up (advisory marker no lock — session-discriminate or lock;
  inspect marker before accepting future same-cell parallel failures), BFM
  non-instantiation recorded acceptable.)
- Task 12: complete (commit 79ee8227d, review APPROVED agent-97 primary: all
  Table 2.8.1 rows mapped+tested unit+rig, AW-only rows structurally W-free,
  B-credit accounting verified sound (AWONLY_ID mux, no leak/double-consume/
  HoQ deadlock), tap refactor verified behavior-preserving, MU/EV never-issued
  assertions real. RULING recorded: AWSNOOP CleanUnique=0x6 (framework 0xB
  collides w/ WriteBack at 3 bits — verified against framework enum); onyx
  task MUST reconcile encodings. WARN x3 accepted as controller-verified/process
  evidence. 5 minors deferred: priority-comment inaccuracy at :330 (safety
  rests on FSM non-overlap — suggest defensive assert), unkillable engine-B
  check at tb:263, rig monitor re-implements base body, stray super_debug flag,
  dead ace_rd_addr/len observational inputs). Area 274/274.
- Task 13: IMPLEMENTATION NOTE — implementer agent-98 burned six 2h caps
  (provider 429s + z3 cover non-convergence); design + docs + 3/4 targets
  green, but control cover hung on `cover: smtbmc z3` (its own sby header
  documents z3 exponential growth on this model; boolector passes). Controller
  took over executional completion (disclosed): root-caused to the engine
  line, verified the final unstaged edits are coherent (prove depth 140→126 +
  txn bound 120→104 keeping ~20cy margin; snoop wrapper tie-off docs), then
  re-ran with current disk state. RESULTS: pfb prove+cover PASS (stand from
  17:50, files unchanged since), victim prove+cover PASS (stand), snoop_resp
  prove+cover RE-RUN PASS 28s with final wrapper, control prove RE-RUN PASS
  (boolector, 68min, depth 126, bound 104), control cover re-running clean
  sequential (concurrent sby tasks on one .sby raced its sqlite status DB —
  controller error, orphaned engine killed). Step 4 divergence check 274/274.
  formal_status --check-flats --staged: 4 CURRENT. Remaining: cover result →
  report verdict → pathspec commit (formal/amber) → task review dispatch.
- QUEUED (user directive, 2026-10-10): deep-research pass on amber's cache
  decisions vs the calibre library at /mnt/data/github/calibre/library/ (186
  author dirs; five target books confirmed: Przybylski Cache+Memory Hierarchy,
  Handy Cache Memory Book 2e, H&P Quantitative Approach, COD RISC-V Edition,
  Harris&Digital Design+CA RISC-V Edition). Deliverable: decisions-alignment
  memo — every amber decision (D1-D12 + fabric/ace-issue choices) mapped to
  book guidance with citations; deliberate educational divergences called out
  as such. Slot: after T13 sign-off, parallel with T14 (research feeds the
  v1.0 doc text).
- INCIDENT (controller error, 2026-10-10): memo commit 95ee1c8fe (docs(riscv-ip)
  swept the staged formal/amber batch (agent-98's 19 paths sat in the index)
  and was pushed before the safety prove completed. Fix-forward only (no
  force-push): content at HEAD is validated POST-HOC by the safety prove;
  T13 close-out carries the true provenance in its docs commit + this ledger.
- INCIDENT (2026-10-10): 10:04 safety prove (bash-ttkq5nvy) zombie-killed —
  its task dir was deleted mid-run (cause unprovable; mechanisms recorded:
  the four amber Makefiles' clean targets rm *_prove/, and any second
  `sby -f` on one task deletes its dir at start). README warns: one sby
  instance per task dir at a time.
- T13 status: final safety prove bash-18r0rtyg... = bash-18r0tyg9 IN FLIGHT
  (depth 126; derived worst-case poison arc 113 + ~11% margin — the earlier
  depth-60 was under-derived, ignored snoop detours; derivation now in the
  sby comment + report). Everything else green: cover 7/7, live prove 80s,
  pf/victim/snoop prove+cover, gates PASS, Step 4 274/274. Close-out on its
  DONE line: report safety row, formal/amber/README.md commit, review seat.
- Deep-research memo: cod-riscv-uarch-alignment.md landed in 95ee1c8fe (the
  memo half of that commit); amber-vs-books full pass still queued for T14.
- T13 CLOSE-OUT (2026-10-10, owner ruling): safety prove verdict ACCEPTED —
  the non-vacuous recorded PASS (boolector, depth 126, bound 104, 68 min, run
  against current disk state; files unchanged since) stands as the task
  verdict. Final clean re-run bash-18r0rtyg9 (launched 11:34) died silently
  ~14:00 at step 55 — INCIDENT #3 (engine PIDs gone, log stops mid-step, no
  FAIL line; box load >10 from unrelated workloads, no OOM evidence readable;
  cause unprovable, mechanism class = the dir-deletion family of (c)).
  Owner ruling: stop re-running on this loaded box; recorded PASS on
  identical content is final. Commits: 0233b6a2d (formal/amber README,
  pathspec, provenance per the 95ee1c8fe incident fix-forward) + sdd docs
  commit (report verdict block, safety row, note (d), this ledger).
  Gate: formal_status --check-flats --staged = checked=0, expected — no
  amber RTL/flats staged; pre-commit flat check ran clean. Review: DISPATCHED
  (see close-out line).
- Deep-research memo (queued user directive): LANDED via agent-100 at
  projects/components/cache-ip/amber-mesi-l1/docs/amber-cache-decisions-alignment.md
  — D1-D11 alignment rows (PRD v0.6 ends at D11; no D12 exists, placeholder
  row records that), CleanUnique=0x6 cited as repo-local divergence, gaps
  G1-G6, bibliography. 4/5 books extracted from calibre markdown
  conversions; H&P ch5 absent from the local conversion (same truncation
  the cod-riscv memo hit) — recorded as gap, not cited. Committed
  separately as docs(cache-ip). Feeds the T14 / v1.0 doc text.
- T13 REVIEW R1 (agent-101, primary): CHANGES-REQUESTED — 4 Important: the
  committed amber_control.sby held the UNDER-DERIVED prove depth 60 (and
  cover 132), not the 126/80 the recorded PASS ran at, so the recorded
  depth-126 safety PASS was not reproducible from the repo. Root cause: the
  staged snapshot swept by 95ee1c8fe predated the controller's depth
  140->126 derivation edits; the derivation never reached the index. All 8
  findings verified against files before fixing. Fixes in 69db03018
  (pathspec formal/amber): prove depth 60->126 with derivation comment,
  cover 132->80, snoop_resp cover engine z3->boolector, wrapper comment
  k-induction -> BMC. Report fixes in the accompanying sdd commit: A-fill-2
  assumption 6->12 cycles (wrapper uses f_fill_wait < 12), data-array
  abstraction wording (ctrl_data_b_rdata / ctrl_cddata tied to 0; values
  unclaimed, not free). Index note: the first fix commit attempt hit a
  shared-trunk index-write race (another session staging mem-ctrl files
  concurrently); commit object landed, index re-synced after. Re-review:
  agent-101 resumed on the delta. OPEN: owner decision on a fresh on-disk
  depth-126 safety run — the repo now reproduces the config; the recorded
  PASS already covers the content.
- T13 REVIEW R1 RE-REVIEW (agent-101): APPROVED with 1 nit. All 8 findings
  RESOLVED; cross-checks consistent (sby/report/README agree on safety 126 /
  cover 80, engines boolector, fill window 12 non-vacuous). Nit: report
  section heading still said "depths are 60 and 126" — fixed editorially in
  this commit. Owner ruling 2026-10-10: no fresh on-disk safety run; the
  recorded non-vacuous PASS stands and the repo now reproduces its config.
  TASK 13 COMPLETE. Commits: 69db03018 (config), 5374b299c (report+ledger),
  this commit (nit + final ledger).
