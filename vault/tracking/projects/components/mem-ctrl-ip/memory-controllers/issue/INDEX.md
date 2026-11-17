<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# memory-controllers — issues

**Next ID: ISSUE-005** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed, spanning more than one
controller (the shared `common-ip` RTL, or pumice and granite together). It
RESOLVES INTO a bug, a task, or a recorded no-action. A problem confined to one
controller is filed in that controller's own lane.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started (the ISSUE-000 template is not counted) |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-002** -- the board's `bank_interleave` map runs at 233-258 MB/s where
  the SKU model sustains 778 on the same streams: ~3.4 MC cycles per beat of an
  RTL-side serialization the scheduling rules do not have. Filed from MC-018,
  2026-11-17.
- **ISSUE-003** -- `close_page` on the board pays ~2.5 MC cycles per dependent
  hop above the SKU model (82-92 against 104-119 MB/s one-bank, 180-240 against
  289-312 bank-parallel): the pipeline's per-hop cost made visible when every
  column is a hop. Filed from MC-018, 2026-11-17.
- **ISSUE-004** -- on `mixed` the SKU model's read turns run four times the
  batch cap (296 / 417 against the board's 272 / 272, union within 9 percent):
  the lane's ACT race on a shared bank after an auto-precharge goes to the
  holder in the model; which RTL term gives it to the waiting direction is the
  question. Filed from MC-018, 2026-11-17.

## Closed

- **ISSUE-001** -- the pumice/granite microarchitecture was ASIC-shaped for an
  FPGA target. Closed 2026-11-08: 12 of 17 resolution rows done (MC-004..MC-010,
  e1ebaacf7 .. a4e9c03f1), 4 deferred with the measurement that says why
  (5, 7, 14b, 15). pumice closes 75 MHz on the FPGA SKU (38,970 LUT, +0.230)
  and runs the board at 75 MHz; granite closes its 75 MHz board point and sits
  on the noise floor at the 100 MHz push profile.
