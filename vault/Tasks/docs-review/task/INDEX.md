<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# docs-review — tasks

**Next ID: TASK-016** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 14 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.

## Closed

- **TASK-001** — fix ALL broken links, whenever they were introduced
- **TASK-002** — emoji sweep: 309 glyphs in 13 tracked .md (843 in 72 files counting code)
- **TASK-003** — every docs/markdown book needs index.md + overview.md
- **TASK-004** — Final MD-only humanize round
- **TASK-005** — Back up or retire the off-repo review collateral
- **TASK-006** — Enable Kimi from the cloud (key + egress)
- **TASK-007** — README rollout: convert 105 beside-code READMEs to link stubs
- **TASK-008** — Final per-section correctness + humanization pass (whole repo)
- **TASK-009** — Fresh per-area qc rounds under the adjudication pipeline
- **TASK-010** — `Testing` section missing from most common and math module pages
- **TASK-011** — The five HAS/MAS books: qc rounds, then humanize
- **TASK-012** — Give math its own docs directory
- **TASK-013** — Validate the finding-adjudication pass (second model) on the next cdc qc round
- **TASK-014** — Humanizer structural-preservation preamble + tag-survival test

## Dropped

- **TASK-015** — Integrate the outstanding Kimi accuracy findings — DROPPED 2026-07-28
