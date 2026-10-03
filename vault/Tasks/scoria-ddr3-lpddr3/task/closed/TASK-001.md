# TASK-001: Advanced scheduling / refresh modes for DDR3/LPDDR3
> Roadmap: `vault/Tasks/memory-controllers/ADVANCED_MODES_ROADMAP.md`
> Migrated 2026-09-25 from `projects/components/scoria-ddr3-lpddr3/TASKS.md` (tooling TOOL-001).

**Priority:** P3 — survey and bounded implementation; not on the board bring-up critical path.
**Status:** CLOSED 2026-10-03. The commodity-legal bounded tranche is implemented behind CSRs and verified (211 FUB + 21 macro + 4 top tests, Verilator + Verible lint green, Modes A/B retention re-proved in formal/scoria); the survey of all eight seeds is in `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/design-requirements.md` "Advanced modes".
**Owner:** TBD

DDR3/LPDDR3 **inherits the DDR2/LPDDR2 commodity baseline** — all scheduling policies, all page policies, REFab, JEDEC ±8 postpone/pull-in scheduling.

- [x] **LPDDR3 per-bank refresh** (`refpb_rr`, REFpb round-robin) — carried forward from the LPDDR2 support; rotor verified in `scoria_refresh_ctrl`.
- [x] The DDR2-paper model-only modes (out-of-order per-bank refresh, write-refresh parallelization, refresh pausing, SARP/DSARP) remain assigned to `ddr4-lpddr4` / andesite, not here.

### [x] SURVEY — DDR3/LPDDR3-specific scheduling / paging / refresh mechanisms

Deliverable completed in `design-requirements.md` "6. Advanced modes": eight candidates surveyed with the commodity-legal vs model-only split, CSR knobs, and named unblock conditions for the deferred items.

Implemented in this task (Modes A-C):

- [x] **Mode A — demand-aware elastic refresh** (`REF_CTRL.elastic_en`, `pullin_idle_streak`, `postpone_demand_streak`). JEDEC ±8 credits unchanged; pull-in confirmed after a configurable idle streak, postpone under sustained demand. Telemetry added to `REF_STATS` postpone/pull-in histogram bins.
- [x] **Mode B — temperature-compensated refresh (TCR)** (`REF_CTRL.tcr_en`, `trefi_derate[1:0]`). Firmware-written derate class (1x/2x/4x) scales the tREFI tick; retention property re-derived with the derate factor.
- [x] **Mode C — ZQCS placement policy** (`ZQ_CFG.placement[1:0]`, `ZQ_CFG.overdue_max`). Policy 0 = baseline request-on-expiry; Policy 1 = defer-under-demand up to `overdue_max`; Policy 2 reserved. Request/grant, never preempt.

Deferred to TASK-009 (unblock conditions from `docs/superpowers/specs/2026-10-03-scoria-advanced-modes-design.md` §6):

- [ ] **RAIDR** — deferred: a retention-profiling path exists (board or model) to feed per-row/bin data; Bloom-filter bin hardware is its own design.
- [ ] **ChargeCache** — deferred: blocked on BUG-003 timing headroom; it makes the arbiter cone hotter.
- [ ] **PARA / Rowhammer targeted refresh** — deferred: after a bitstream exists, with a Rowhammer test methodology; adjacency tracking is its own design.
- [ ] **SALP** — deferred: belongs to andesite (DDR4/LPDDR4) per the task's own split.
- [ ] **Self-refresh / power-down scheduling** — excluded by the recorded 2026-09-30 HAS decision; re-opened only by the owner.

## Verification landed with this close-out

- Functional regression: 211 FUB + 21 macro + 4 top tests green (`make run-all-func`).
- Lint: Verilator (54 modules) + Verible green (`make lint-all`).
- Formal: Modes A/B retention properties re-proved in `formal/scoria/refresh_ctrl`; cover for pull-in at configured streak boundary.
- Timing: BUG-003 OOC synthesis re-measured with the new RTL; numbers appended to BUG-003.md. The arbiter pick cone did not change.

## Not in scope

The research-grade mechanisms (RAIDR, ChargeCache, PARA, SALP, power-down) are not implemented; they are filed as TASK-009 with their unblock conditions. No scoria MAS was authored by this work.
