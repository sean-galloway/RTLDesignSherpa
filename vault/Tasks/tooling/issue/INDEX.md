<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

None.

## Closed

- **ISSUE-003** — CLOSED (recorded no-action, 2026-10-08): cocotb-framework major-rev
  advisory fully absorbed — package at 1.2.1 (IRQ BFM promotion intact), the carried
  `cocotb-coverage<2` gap lifted and validated under TASK-029, and the shared-venv
  flip removes the last pre-1.0.0 venv. Owner-confirmed closure.

- **ISSUE-002** — CLOSED: the compound `<codename>-<protocols>` form is the
  directory name at every level (component dir, task area, knowledge mirror). All
  three memory-controller areas renamed and promoted to top level; the rule is
  stated in the memory-controllers README. Prose citations keep the bare codename,
  on purpose.

- **ISSUE-001** — Triage the 18 Dependabot vulnerabilities on the default branch
