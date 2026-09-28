<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB/hpet — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 2 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-003** — legacy PC/AT replacement routing; the `legacy_replacement` CSR is built and wired, the IRQ routing it gates is not.

## Closed

- **TASK-001** — Timer 2+ not firing in multi-timer tests; a test-cleanup defect, fixed 2025-10-17.
- **TASK-002** — comparator reads returned the last software-written value, not hpet_core's live advancing comparator; fixed with `hw=rw` + `precedence=sw`, closed 2026-09-27.

## Dropped

- **TASK-005** — no HPET integration examples
- **TASK-004** — 64-bit counter read is not atomic
