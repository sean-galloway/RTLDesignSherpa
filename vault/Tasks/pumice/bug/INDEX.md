<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# pumice — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **BUG-000** — TEMPLATE — copy this file, never file against it

## Closed

- **BUG-003** — an arbiter pick rejected by its own final safety gate
  (`w_out_safe==0`) was pushed to the cmd FIFO and executed by the DRAM, while
  `w_fire_out` withheld `evt_*` so the bank timers never saw it — FIXED
  2026-09-27, one line in `pumice_cmd_arbiter.sv`
- **BUG-001** — one unattributed mismatched beat, seen once in 1008 matrix cells
- **BUG-002** — close-page below its command-bus ceiling — FIXED 2026-09-25,
  62.8% -> 85.7% via bank-timer lookahead + final-stage timing authority
  (silicon-confirmed +32.8%); residual is the in-order pick pipeline, the
  documented design point
