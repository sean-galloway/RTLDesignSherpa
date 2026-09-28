<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB/hpet — bugs

**Next ID: BUG-003** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.

## Closed

- **BUG-002** — the HPET report's `timer_functionality_verified` and `total_tests_run` could never be true (fixed: real per-subtest counts, and a timer event recorded on each rising timer_irq; 25/25 at FULL, 4/4 at GATE)

- **BUG-001** — 8-timer non-CDC "All Timers Stress" timeout: NOT REPRODUCIBLE, both configs pass 4/4; the `timeout = 50000` it told us to bump does not exist
