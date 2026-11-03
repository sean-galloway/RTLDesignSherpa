<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# amber — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between state is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Closed

- **TASK-001** ([page](closed/TASK-001.md)) — G2 rig measurement upgrade:
  tally clear/freeze CSR wiring, injector latency counters, 16-deep
  re-armable latch bank, RDL entries for the latch readback. All four items
  landed 2026-11-01/02; board rebuild + sweep re-run pending (needs the
  Genesys 2). Clears jet T13's blocker.
