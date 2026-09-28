<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.

## Closed

- **BUG-001** — regblock reset polarity composed by hand
- **BUG-002** — SYNCASYNCNET under -DRESET_ACTIVE_HIGH, family-wide
- **BUG-003** — an unmapped APB address hung the RLB bus
