<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# site-audit — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **TASK-002** — teach the checker to see BOTH directions (the 11-task triage is done) — CLOSED 2026-10-04

- **TASK-001** — Site-wide audit: RTL correct, docs match, docs humanized, verification covers it
