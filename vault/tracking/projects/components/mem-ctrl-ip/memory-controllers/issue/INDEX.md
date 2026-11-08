<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# memory-controllers — issues

**Next ID: ISSUE-002** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed, spanning more than one
controller (the shared `common-ip` RTL, or pumice and granite together). It
RESOLVES INTO a bug, a task, or a recorded no-action. A problem confined to one
controller is filed in that controller's own lane.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started (the ISSUE-000 template is not counted) |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **ISSUE-001** -- the pumice/granite microarchitecture was ASIC-shaped for an
  FPGA target. Closed 2026-11-08: 12 of 17 resolution rows done (MC-004..MC-010,
  e1ebaacf7 .. a4e9c03f1), 4 deferred with the measurement that says why
  (5, 7, 14b, 15). pumice closes 75 MHz on the FPGA SKU (38,970 LUT, +0.230)
  and runs the board at 75 MHz; granite closes its 75 MHz board point and sits
  on the noise floor at the 100 MHz push profile.
