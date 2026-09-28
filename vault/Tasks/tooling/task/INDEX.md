<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — tasks

**Next ID: TASK-014** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 7 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-013** — source comments still cite pre-migration task IDs
- **TASK-002** — Finish validating the cloud bootstrap on a genuinely clean box
- **TASK-003** — Two real gaps in the RDS-DV arbiter BFM
- **TASK-004** — Project-area cleanup — apply the RTL-area pattern to projects/
- **TASK-005** — Tests resolve filelists through the toml registry, not hardcoded paths
- **TASK-006** — emit CONTRACT TABLES (proofs), not K-map pictures
- **TASK-000** — reserved template; copy the file, do not file against it.

## Active

- **TASK-001** — Migrate the remaining areas into /vault/Tasks/<area>/

## Closed

- **TASK-007** — Migrate the remaining method docs out of bin/ into the handbook
- **TASK-008** — One gate that runs filelist_registry --check and --audit
- **TASK-009** — Redo the Makefiles from scratch
- **TASK-010** — Cohesive SKILLS strategy for the repo
- **TASK-011** — Burn down --blindspots, then make it a gate
- **TASK-012** — `formal/` has two competing conventions for where sv2v lives
