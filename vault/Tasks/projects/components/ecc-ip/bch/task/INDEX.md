<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/bch — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
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
- **TASK-002** — Author the BCH HAS v0.1: the `docs/bch_has/` architecture
  specification mirrors the reed-solomon HAS; closes when the v0.1 PDF builds
  and every open item is tied to a PRD decision ID.

## Closed

## Deferred
