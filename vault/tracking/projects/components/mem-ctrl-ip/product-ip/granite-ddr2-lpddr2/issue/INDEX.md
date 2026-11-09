<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — issues

**Next ID: ISSUE-003** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

None.

## Active

- **ISSUE-002** -- granite does not come up on the Nexys at 100 MHz (2026-11-09):
  no read eye through the controller on every placement built that day, the
  2026-11-02 design included; granite at 75 MHz and LiteDRAM at 100 MHz pass on
  the same board. Blocks the 100 MHz LiteDRAM comparison (memory-controllers
  MC-011). [active/ISSUE-002.md](active/ISSUE-002.md).

## Closed

- **ISSUE-001** — same-id writes to different banks can return their B responses
  out of AXI order. Found by reading the store 2026-11-03; REPRODUCED 2026-11-05
  by the directed B-order test and re-filed as [BUG-001](../bug/closed/BUG-001.md).
  Closed 2026-11-06. [closed/ISSUE-001.md](closed/ISSUE-001.md).
