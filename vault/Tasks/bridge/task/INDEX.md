<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.

## Dropped

- **TASK-001** — trim method from `bridge/CLAUDE.md`; dropped, the file was already compliant and every row of its removal table was falsified by reading the text.
