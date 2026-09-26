<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — tasks

**Next ID: TASK-014** — never recycle a number, even when its item closed.

Planned work we decided to do: a feature, a refactor, a migration, a cleanup. It starts from INTENT -- nothing is wrong, we want something different.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 4 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 9 | done (kept for history) |
| [dropped/](dropped/) | 2 | ended without completing |

## Open

- **TASK-000** — TEMPLATE — copy this file, never file against it
- **TASK-009** — doc + filelist cleanup (push from workstation)
- **TASK-013** — adapt predictors (modes 4/5) are inert on everything measured,
  but their triggers may never have fired; test before retiring

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
- **TASK-010** — per-generator Scenario override in measure_concurrent; the
  hardware always allowed it, only the host collapsed N generators to N copies
- **TASK-011** — RBL measured on the workload built for it: mode 6 is strictly
  worse than mode 7, mode 7 is bit-identical to no predictor; 5,578 LUT unearned
- **TASK-002** — all three axes on silicon: reordering is worth 3.9x, every
  predictor is inert, refresh costs 4.7% and tREFI is the only tunable that pays

## Dropped

- **TASK-003** — was a RULE filed as a task; moved to
  `vault/handbook/dv/running-regressions.md`
- **TASK-004** — was the AT REST handover filed as a task; moved to
  `projects/components/memory-controllers/pumice-ddr2-lpddr2/CLAUDE.md`
