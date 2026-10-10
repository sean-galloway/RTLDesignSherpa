<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# math — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-003** — required-regen fixes can drag unrelated changes into a
  commit (dates + stale templates); mitigation protocol: reconcile drift
  (ISSUE-002), stop date-stamping regens, surgical-revert protocol, optional
  regen-cleanliness CI gate
- **ISSUE-002** — full ieee754 generator regen produces ~115 files of drift
  (Created-date stamps + stale reset-macro template vs committed RTL); needs a
  one-time reconcile so future regens are no-op diffs

## Closed

- **ISSUE-001** — Decide: bf16 multiplier rounding is not RNE — intended or RTL defect?
