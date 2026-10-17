<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amber — bugs

**Next ID: BUG-005** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **BUG-004** ([page](closed/BUG-004.md)) — G2 harness drove the MonBus group filter
  masks all-ones; the group reads them as drop masks, so the tally counted
  nothing (board + sim, never before asserted). CLOSED 2026-10-16: masks
  -> 16'h0000, group flush watermark 16'hFF00 -> 48 (drain was ~4x under
  arrival rate; ~11.2k/11.2k records delivered post-fix), tally profile
  re-keyed from wire truth, cosim asserts sum(bins) > 0, board perf sweep
  verified.
- **BUG-003** ([page](closed/BUG-003.md)) — amber Genesys2 board read hang:
  Vivado synthesis folded the UART-to-bridge AR handshake.
- **BUG-002** ([page](closed/BUG-002.md)) — pair rig full: deterministic
  cross-cache deadlock at SEED=45207 (MISS_FILL x SNOOP).
- **BUG-001** ([page](closed/BUG-001.md)) — miss_fill_macro func cell: 3-check divergence
  at one lockstep transaction. CLOSED 2026-10-15: not reproducible at HEAD —
  full 48-worker grid (350/350) + recorded seed solo (4/4) + forced-load (6/6)
  all green; corner plausibly removed by BUG-002 PF_GUARD (`ab308d108`), which
  post-dates the failure and reworks the soaked interaction. Archive-before-
  rerun instruction survives in the filing.
