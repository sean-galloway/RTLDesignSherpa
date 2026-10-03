<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — tasks

**Next ID: TASK-028** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 25 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-027** (P3) — 43 broken testplan refs outside pumice (val/common 32,
  fabric-gen-ip 9, val/amba 2): fix per area with pumice TASK-037's
  update-or-delete judgment, then lower the ratcheted baseline
  (`filelist_registry.py --testplans --update-testplan-baseline`). The gate
  added by TASK-037 makes any NEW broken ref fail pre-commit/CI

- **TASK-025** (P3) — cocotb 2.x is reachable but not yet: the import blocker is cocotb-bus 0.2.1 (fixed by 0.3.0, which our own DV cap forbids), and the remaining work is a 78-site `.value.integer` sweep across both repos



## Active


## Closed

- **TASK-026** — formal stale-flat self-detection, fanned out of rapids
  BUG-011 -- CLOSED 2026-10-03: `bin/formal_status.py --check-flats`
  re-flattens via each proof's own recipe (or its house check-flat target)
  and diffs whitespace-normalized, never writing the tree; pre-commit
  `--staged` gate plus a repo-wide CI job (sv2v pinned v0.0.13) and a
  planted-staleness pytest. Repo-wide run: 139/139 CURRENT; 12 stale flats
  regenerated; 68 Makefiles gained check-flat; two Makefiles repaired
  (axi4_to_apb4_shim's cdc paths, stream_core's env exports); pumice-style
  gitignored areas skip by design.
- **TASK-020** — pilot cocotb-test 0.3.0, then decide whether cocotb 2.x is reachable -- CLOSED 2026-10-01: 1000/1000 identical across val/amba, bridge and stream on the same seed with only cocotb-test moved; requirements.txt bumped 0.2.5 -> 0.3.0 and the shared venv synced. Question 2 answered with measurements and filed as TASK-025
- **TASK-022** (P1) — the FPGA flow lock was keyed on the build directory, and nothing detected a collision that happened anyway -- CLOSED 2026-10-01: board-keyed lock, shared identity readback, and the verdict persisted beside the bitstream sha256; hardware path verified on the Genesys 2 (readback 5.8s, real program 16.5s, wrong-board refusal rc=1, sha256 matches). The live output exposed that the test fixture was a chain real hardware cannot produce: 0 of 25 tests caught an exact-match regression, 7 of 26 do now
- **TASK-024** — fpga-systems was the only major area with no book -- CLOSED 2026-09-30: 19 chapters in 6 chapters + 5 mermaid diagrams, FPGA_SYSTEMS_MAS_v1.0.pdf (48 pages); the filed premise of "three competing conventions" was WRONG and is corrected in the task -- there is one convention, documented in flow-layout.md AND make/fpga_flow.mk, whose prefixes are load-bearing because make and SequenceRunner.discover glob them; `flows-*` is the pre-migration layout
- **TASK-023** — `env_python` resolved its own root from where the CALLER stood, so it could silently activate another repo's venv -- CLOSED 2026-09-30: REPO_ROOT from BASH_SOURCE, worktrees share the main checkout's venv via --git-common-dir, a missing venv fails with rc=1; 5-case matrix measured before/after under `env -i`, plus a real 20.43s sim
- **TASK-021** — cocotb-framework's `__version__` drifted from pyproject for six releases (published 0.6.7 self-reported 0.6.1) -- CLOSED 2026-09-30: setuptools dynamic version in RDS-DV `4713ef8` makes the module literal the single source; 5-test guard + a `unit-tests` CI job; verified live (1509 passed, ZERO skips) and mutation-tested 4 ways
- **TASK-019** — filelist_utils.tcl exists as eight copies and seven do not treat // as a comment -- CLOSED 2026-09-29: one make/tcl/filelist_utils.tcl sourced by all 8 flows + the Quartus sweep; 7 copies deleted; Tcl/Python agreement test
- **TASK-018** — `formal/Makefile`'s `formal:` list reaches every area except `apbx_xbar` (5 proofs) and `bridge` (1), so 6 proofs never run unattended; the same file's comments warn about exactly this omission twice already. -- CLOSED 2026-09-29: formal-apbx-xbar + formal-bridge in the formal: list; area Makefiles discover <dir>/<dir>.sby; 7/7 tasks PASS=14
- **TASK-016** — fan out the 8 doc-example findings the widened gate surfaced (converters x3, stream/regs, fpga-systems/boards); each needs its owner to triage as defect or illustrative. -- CLOSED 2026-09-29: fanned out to converters TASK-004 and stream TASK-015; the lane-less fpga-systems debounce example fixed in place; BASELINE 7
- **TASK-015** — check_task_ids.py runs only in pre-commit; no CI step validates the tracker, so a --no-verify commit or an uninstalled hook lands a lying tracker unchecked. -- CLOSED 2026-09-29: check_task_ids runs in the filelists CI job; 5 teeth tests in bin/tests prove it fails on each planted defect
- **TASK-017** — filelist_registry reads the toml and baselines from the worktree while the hook's file set comes from the temporary index -- a peer's staged move fails everyone's commit -- CLOSED 2026-09-28: in hook context the toml and baselines come from the index being committed; reproduced old-fail/new-pass in a scratch clone
- **TASK-014** — check_task_ids.py reconciles INDEX state counts against the directories -- CLOSED 2026-09-28: count rows are errors when they disagree with disk; mutation-tested 3 ways
- **TASK-004** — Project-area cleanup — apply the RTL-area pattern to projects/ -- CLOSED 2026-09-28: --placement ratchet in CI, RLB filelists moved, 4 stale shared guides retired; per-unit remainder filed as rapids TASK-017, pumice TASK-032, stream TASK-013, bridge TASK-012, converters TASK-003, misc TASK-004, RLB TASK-016, timing_characterization TASK-005
- **TASK-006** — emit CONTRACT TABLES (proofs), not K-map pictures -- CLOSED 2026-09-27: the bin/kmaps emitter is complete; per-unit remainder filed as pumice TASK-029 and stream TASK-012
- **TASK-013** — source comments still cite pre-migration task IDs -- CLOSED 2026-09-27: 1,199 + generator citations swept; pumice's 173 filed as pumice TASK-030
- **TASK-005** — Tests resolve filelists through the toml registry, not hardcoded paths -- CLOSED 2026-09-27: filelist_for() + module= mode, 353 val tests migrated, 6 unit tests
- **TASK-003** — Two real gaps in the RDS-DV arbiter BFM -- CLOSED 2026-09-27: both fixed in RDS-DV 784f905 (real RR scoring + burst detection, shared-catalogue and saturating profiles); venv refresh is the owner's call
- **TASK-002** — Finish validating the cloud bootstrap on a genuinely clean box -- CLOSED 2026-09-27: ran end to end in a clean ubuntu:24.04 container; fixed the unconditional sudo, added unzip, fixed the tool report
- **TASK-001** — Migrate the remaining areas into /vault/Tasks/<area>/
- **TASK-007** — Migrate the remaining method docs out of bin/ into the handbook
- **TASK-008** — One gate that runs filelist_registry --check and --audit
- **TASK-009** — Redo the Makefiles from scratch
- **TASK-010** — Cohesive SKILLS strategy for the repo
- **TASK-011** — Burn down --blindspots, then make it a gate
- **TASK-012** — `formal/` has two competing conventions for where sv2v lives

## Deferred

