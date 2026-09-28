<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/misc — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — all RDL lives in the rdl directory
- **TASK-000** — reserved template; copy the file, do not file against it.

## Closed

- **TASK-002** — scrub the tests for completeness (misc)
