<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# coverage — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-002** — Bring the last three test areas onto the base coverage path

## Closed

- **TASK-001** — Coverage infrastructure consolidation (historical record)

## Dropped

- **TASK-003** — delta has five RTL files, no tests at all, and two copies of one module
