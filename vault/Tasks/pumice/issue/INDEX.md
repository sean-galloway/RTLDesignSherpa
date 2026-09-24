<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — issues

**Next ID: ISSUE-005** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **ISSUE-000** — TEMPLATE — copy this file, never file against it
- **ISSUE-001** — read latency is ~2x LiteDRAM's, and it caps small-burst reads
- **ISSUE-002** — close-page modes reach only ~63% of their own command-bus ceiling

## Closed

- **ISSUE-003** — SCHED_WR_WM.wr_batch_max may clobber the whole register on write
- **ISSUE-004** — the +25-30% batching gain was measured with the broken drain
