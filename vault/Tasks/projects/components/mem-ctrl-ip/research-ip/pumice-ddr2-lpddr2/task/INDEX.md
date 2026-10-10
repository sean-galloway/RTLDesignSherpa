<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — tasks

**Next ID: TASK-043** — never recycle a number, even when its item closed.

Planned work we decided to do: a feature, a refactor, a migration, a cleanup. It starts from INTENT -- nothing is wrong, we want something different.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 34 | done (kept for history) |
| [dropped/](dropped/) | 4 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open

- **TASK-042** — LPDDR2 board enablement: from "vaguely supported" to fully
  enabled for the incoming LPDDR2 board -- runtime ZQ calibration (first
  content of `pumice_training_layer` per the owner's MC-001 ruling), board
  timing/CSR definition, BFM/DV gap check, bring-up harness, and REFpb
  runtime exercise.

## Deferred

- **TASK-033** — the v2/v3 power and mode-register deferrals (6 RTL TODO markers).
  Parked pending the DDR3/LPDDR3 (`scoria`) project, where several are likely to
  be taken up instead. The `dfi_init_complete` interlock inside it does NOT
  depend on scoria and is a test, not a feature

## Closed

- **TASK-035** — CLOSED 2026-10-08: tier 1 proven, all four done-criteria on
  every tier-1 block; area at 21/21 sby tasks. `dfi_cdc` finished (token/data
  pairing, no-beat-lost/duplicated, init semantics; 13/13 covers, 8/8
  mutations) and `wr_data_cam` finished (commit data integrity via a
  drain-queue attribution model, framing/lifecycle; 9/9 covers, 3/3
  mutations; the old readback counterexample refuted as a wrapper bug). The
  campaign's load-bearing discovery: yosys 0.62 resolves dotted `dut.*`
  refs to FREE INPUTS — the injected-probe-port pattern (dfi_cdc's
  inject_probes.py) replaces them; the rest of the area audits clean. No RTL
  defects. Tier 2/3 explicitly out of scope per the item's own definition of
  done.

- **TASK-038** — CLOSED 2026-10-04: both ddr2-char harnesses rebuilt on the
  post-sdpram-fix tree (pumice `61d35ff7` +0.132 ns, LiteDRAM `44a1b836`
  +0.321 ns, one commit, all smokes green) and every board-measured figure
  repinned. Fix is off the char datapath: LiteDRAM within 25 read-cycles of
  09-10 on 13/14 points (worst row 0.22%), pumice streaming within +0.2%; the
  A/B headline moves anyway
  (pumice reads at LiteDRAM parity page-friendly; 1.6-2.5x behind same-bank
  thrash; concurrent 2.00x/1.80x re-measured BOTH sides 2026-10-04). Knee
  (PUMICE-036) spot-checked 48 pts post-fix — did not move (4+4 to the digit).
  Cosim needs no re-baseline (no windows exist); uart suite 12/12 post-fix.
  Docs: post-fix numbers or dated pre-fix notes across AT-A-GLANCE, HAS/MAS,
  design-requirements, the A/B findings chain, the char guide; dated records
  (closed tasks, generated CSR docs) left as-is by ruling

- **TASK-039** — CLOSED 2026-10-03: the 13 post-rearchitecture testplans
  authored (63 scenarios: cmd_arbiter, bank_timers, rd/wr intakes,
  wr_data_cam, rd_return_ring, wr_splitter, axi4_ifc, the DFI stack) +
  SCHED-24 sched_matrix scenario; README inventory 11 -> 24 plans,
  rollup 100 -> 164 scenarios, no-plan rationale for the exceptions.
  Also fixed scheduler_testplan's stale test_file path (fub -> macro;
  ratchet baseline re-lowered 43 -> 42) and its four phantom parameters

- **TASK-037** — CLOSED 2026-10-03: the 16 stale `dv/testplans/` reconciled
  with the modules that exist — 3 renamed in place (scheduler ->
  pumice_mem_cmd_scheduler, rd_cmd_cam -> pumice_rd_cmd_cam, page_predictor ->
  pumice_page_policy), 13 deleted as dissolved (axi_intake split, wr_cmd_cam,
  xbank_timers, the six macro wrappers, ...), 25 -> 12 plans, README rewritten
  to the same truth. The parser check the task was really about now exists:
  `filelist_registry.py --check` gates every `*_testplan.yaml` ref repo-wide,
  ratcheted (43 pre-existing refs outside pumice are tooling TASK-027). Filed
  pumice TASK-039 for the coverage gap the reconcile exposed

- **TASK-036** — CLOSED: both questions answered. At the PHY layer the FPGA's DQ
  drive never coincides with a read window at tRTW=3 and stays **28 cycles
  clear** (instrument proven: each probe fires alone, only the conjunction is
  silent), and the predicted danger point at tRTW≈12 shows no contention either.
  The model is conservative in shape; `rtw_guard` guards against nothing. Taking
  the +76% (246 → 435 MB/s total at gap 14) is now a decision with the evidence
  in hand, not an investigation

- **TASK-034** — CLOSED: option 1, document and keep. The N+1 convention is
  documented (RDL + regen, MAS, HAS, `a_*_bound_n1` properties). The board
  campaign showed this design's turnaround can be cut by 17 cycles with no
  observable effect, so one cycle on each of ten windows does not justify an RTL
  change; the real bandwidth question became [[TASK-036]]

- **TASK-032** — placement pass: 2 loose filelists into `rtl/filelists/` (baseline
  8 -> 6, no pumice entries) and 8 markdown files re-homed, 43 references repointed

- **TASK-015** — the 4-layer config-coverage plan: reset-parity gate (L0),
  pairwise covering array 39 vectors / 105 of 105 pairs at each of 4 gaps,
  312 cells (L1), telemetry invariants (L2b), seeded random soak (L3).
  L2a dropped: no assertions in RTL

- **TASK-029** — all 17 signal-contract maps carry a sufficiency argument and
  the 14 two-valued ones an RTL verdict: 12 IDENTICAL, 2 DIFFERS (both redundant
  terms the bank timer already implies, justified and kept)

- **TASK-031** — ddr2_char's clean target uses the marker-aware cleaner (the last
  raw `rm -rf local_sim_build` in the repo)

- **TASK-030** — repointed 162 of 171 legacy tracker-id citations
  against MIGRATION_MAP.md (59 files; lint clean, comment-only in RTL). 9 left
  with no migration target (`PUMICE-018` x7, `PUMICE-PERF` x2) — needs a
  disposition, not a sweep
- **TASK-028** (was `PUMICE-KMAP`) — real K-maps for the scheduler, CAMs and DFI layer
- **TASK-017** (was `PUMICE-005`) — Board reads WORK: validated tuple + honest measurement
- **TASK-018** (was `PUMICE-007`) — Retire the deskew RTL + PHY_TIMING.deskew_lo/hi CSR
- **TASK-020** (was `PUMICE-009`) — Generic AXI data-width gearing
- **TASK-021** (was `PUMICE-010`) — Single-register AXI-address -> {bank,row,col} mapping
- **TASK-022** (was `PUMICE-011`) — Full LPDDR2 mode-register init
- **TASK-023** (was `PUMICE-014`) — retire ALL hand-poking of valid/ready interfaces in pumice DV
- **TASK-024** (was `PUMICE-015`) — greppable structure trackers (CAMs / page policy / refresh / scheduler)
- **TASK-026** (was `PUMICE-022`) — board validation: WRITE TARGET MET (570 MB/s), READ CEILING FOUND
- **TASK-027** (was `PUMICE-026`) — finish the LiteDRAM same-harness A/B (it is already ~80% built)

- **TASK-016** — nothing checks the DDR2 init sequence for JEDEC legality;
  the matrix excludes it because the init waits are shortened for sim, so
  init command order/content is unverified at every level

- **TASK-014** — the adaptive page modes need a disposition: retire mode 4
  (it IS fixed_open(tr_min)), re-plumb mode 5's verdict to the background
  precharge, and add predictor observability first

- **TASK-013** — page-policy campaign: closing pages early is worth up to +41.2%
  and the mechanism is the background precharge, not a predictor. Mode 4 is
  fixed_open(tr_min); mode 5 mis-plumbed. Default change blocked on BUG-003
- **TASK-005** — the paging predictors are built unconditionally and the board never uses them
- **TASK-006** — no stall-cause attribution, so the overhead breakdown cannot be published
- **TASK-008** — no test bounds the write drain, and the cap is unreachable at the shipped watermarks
- **TASK-001** — QoS + advanced scheduling: mechanisms complete, all three
  reported gaps dispositioned (P1+P3 fixed, P2 re-filed as TASK-012)
- **TASK-007** — write batching: corruption fixed (3 defects, 210 clean board
  runs, +12.2% bus); wire-level JEDEC audit now gates the spacing
- **TASK-012** — axis 3 is MEASURED now: REF_STATS_REF_BUSY counts refreshes
  that fired with work pending, so host idle time cannot contaminate it
- **TASK-010** — per-generator Scenario override in measure_concurrent; the
  hardware always allowed it, only the host collapsed N generators to N copies
- **TASK-011** — RBL measured on the workload built for it: mode 6 is strictly
  worse than mode 7, mode 7 is bit-identical to no predictor; 5,578 LUT unearned
- **TASK-002** — all three axes on silicon: reordering is worth 3.9x, every
  predictor is inert, refresh costs 4.7% and tREFI is the only tunable that pays
- **TASK-009** — tb filelists moved to dv/filelists/; doc placement was already
  compliant, and the gate it was deferred behind no longer applied

## Dropped

- **TASK-019** (was `PUMICE-008`) — Per-beat DFI read deskew
- **TASK-025** (was `PUMICE-016`) — adopt axi4_intf_master_observer (APB-configured) for perf observation

- **TASK-003** — was a RULE filed as a task; moved to
  `vault/handbook/dv/running-regressions.md`
- **TASK-004** — was the AT REST handover filed as a task; moved to
  `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/CLAUDE.md`
