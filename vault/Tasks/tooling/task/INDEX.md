<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — tasks

**Next ID: TASK-014** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 12 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.

## Active


## Closed

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

- **TASK-004** — Project-area cleanup — apply the RTL-area pattern to projects/ -- DEFERRED by Sean until the RTL area is complete
