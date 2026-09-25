<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — tasks

**Next ID: TASK-013** — never recycle a number, even when its item closed.

Planned work we decided to do: a feature, a refactor, a migration, a cleanup. It starts from INTENT -- nothing is wrong, we want something different.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 5 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 2 | ended without completing |

## Open

- **TASK-000** — TEMPLATE — copy this file, never file against it
- **TASK-002** — characterize + tune the advanced modes (all three axes)
- **TASK-009** — doc + filelist cleanup (push from workstation)
- **TASK-010** — no generator config can show RBL a win, and the harness is what blocks it
- **TASK-011** — build generator patterns that can show RBL a win

## Closed

- **TASK-005** — the paging predictors are built unconditionally and the board never uses them
- **TASK-006** — no stall-cause attribution, so the overhead breakdown cannot be published
- **TASK-008** — no test bounds the write drain, and the cap is unreachable at the shipped watermarks
- **TASK-001** — QoS + advanced scheduling: mechanisms complete, all three
  reported gaps dispositioned (P1+P3 fixed, P2 re-filed as TASK-012)
- **TASK-007** — write batching: corruption fixed (3 defects, 210 clean board
  runs, +12.2% bus); wire-level JEDEC audit now gates the spacing
- **TASK-012** — axis 3 is MEASURED now: REF_STATS_REF_BUSY counts refreshes
  that fired with work pending, so host idle time cannot contaminate it

## Dropped

- **TASK-003** — was a RULE filed as a task; moved to
  `vault/handbook/dv/running-regressions.md`
- **TASK-004** — was the AT REST handover filed as a task; moved to
  `projects/components/memory-controllers/pumice-ddr2-lpddr2/CLAUDE.md`
