<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — bugs

**Next ID: BUG-002** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

None.

## Active

None.

## Closed

- **BUG-001** — same-id write B responses leave out of AXI order across banks:
  B order is commit order and the pick has no id term. Reproduced 2026-11-05
  (8 / 12 backtoback, 4 / 12 constrained); was ISSUE-001. Recommended fix: an
  AW-order B release queue, which also closes memory-controllers BUG-001.
  Fixed 2026-11-06 by that queue (Bs leave in AW order for all ids, no id
  compare, pick untouched); closed 2026-11-07. [closed/BUG-001.md](closed/BUG-001.md).
