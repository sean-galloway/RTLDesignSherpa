<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/apbx-xbar — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Closed

- **BUG-001** — raw-address slave decode rotated the map for any non-span-aligned BASE_ADDR
- **BUG-002** — out-of-range addresses wedged the master forever

## Dropped

- **BUG-003** — apbx_xbar_thin presents NO setup phase downstream (PSEL and PENABLE assert together)
