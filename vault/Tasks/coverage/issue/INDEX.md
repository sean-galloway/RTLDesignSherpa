<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# coverage — issues

**Next ID: ISSUE-002** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

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

## Open

- **ISSUE-001** — coverage data collection is unwired repo-wide:
  `coverage-report` runs but reports 0% almost everywhere; only val/common
  and pumice-fub pass Verilator's --coverage flags (surfaced closing
  TASK-002; the three TASK-002 areas wired by hand as the reference)

