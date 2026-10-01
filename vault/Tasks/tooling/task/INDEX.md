<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — tasks

**Next ID: TASK-025** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 20 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-020** — pilot cocotb-test 0.3.0 (it removes the `cocotb.config` import that makes cocotb 2.x a landmine for every cocotb_test-based test in the tree), then decide whether cocotb 2.x is reachable at all
- **TASK-023** (P2) — `env_python` resolves its own root with `git rev-parse --show-toplevel`, so sourcing it from another repo's tree silently activates THAT tree's venv; from the RDS-DV tree it imports a stale 0.6.7 snapshot that self-reports 0.6.1, which is the mechanism behind a real misdiagnosis of 9 test failures
- **TASK-022** (P1) — the FPGA flow lock is keyed on the build directory, so two areas can drive one board; a harness records the sha256 it programmed rather than what is on the device, so a mid-run reprogram publishes someone else's measurements with no error at all



- **TASK-024** (P2) — `projects/fpga-systems/` is the only major area with no book, and it is the layer every board flow imports; document the UART flow end to end plus the host/seq naming conventions, including the THREE coexisting directory layouts nothing currently chooses between


## Active


## Closed

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

