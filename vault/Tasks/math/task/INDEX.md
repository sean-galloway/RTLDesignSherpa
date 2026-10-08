<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# math — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 5 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Closed

- **TASK-005** — IEEE 754 gradual underflow (SUBNORMAL_SUPPORT) across the
  ieee754 family + new fp32 divider and sqrt (CLOSED 2026-10-07; commits
  cf9520e2b, 0dc286dbd, f0b5e3f3f, 065148c0a, 02140c782)
- **TASK-004** — scrub the tests for completeness (math)
- **TASK-001** — filelist coverage: 134 math modules have no .f; 106 of 119 math tests hand-list sources
- **TASK-002** — math_mod_3_compress needs its final formal checks
- **TASK-003** — Re-run the full math formal suite after the path repair
