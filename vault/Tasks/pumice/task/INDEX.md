<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — tasks

**Next ID: TASK-010** — never recycle a number, even when its item closed.

Planned work we decided to do: a feature, a refactor, a migration, a cleanup. It starts from INTENT -- nothing is wrong, we want something different.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 10 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **TASK-000** — TEMPLATE — copy this file, never file against it
- **TASK-001** — QoS + advanced scheduling (post-cleanup)
- **TASK-002** — characterize + tune the advanced modes (all three axes)
- **TASK-003** — the char-framework sim is the board gate and must run before any pumice RTL commit
- **TASK-004** — pumice is AT REST: what a future session needs to know
- **TASK-005** — the paging predictors are built unconditionally and the board never uses them
- **TASK-006** — no stall-cause attribution, so the overhead breakdown cannot be published
- **TASK-007** — batch same-direction columns to amortise the R/W turnaround
- **TASK-008** — no test bounds the write drain, and the cap is unreachable at the shipped watermarks
- **TASK-009** — doc + filelist cleanup (push from workstation)
