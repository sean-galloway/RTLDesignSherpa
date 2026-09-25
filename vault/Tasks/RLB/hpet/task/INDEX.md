<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB/hpet — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 5 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-002** — comparator registers are write-only; software cannot read back programmed values.
- **TASK-003** — legacy PC/AT replacement routing; the `legacy_replacement` CSR is built and wired, the IRQ routing it gates is not.
- **TASK-004** — 64-bit counter read is not atomic; LO-then-HI can straddle an increment.
- **TASK-005** — no HPET integration examples exist under `docs/hpet_mas/`.

## Closed

- **TASK-001** — Timer 2+ not firing in multi-timer tests; a test-cleanup defect, fixed 2025-10-17.
