<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/bch — tasks

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
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Active

## Open

- **TASK-001** — Stand up the BCH component: references gathered and draft
  PRD v0.1 landed 2026-10-03; HAS, RTL + DV, board harness to follow. Runs
  the way reed-solomon TASK-001 ran — closes when the component exists and
  passes end to end.

## Closed

## Deferred
