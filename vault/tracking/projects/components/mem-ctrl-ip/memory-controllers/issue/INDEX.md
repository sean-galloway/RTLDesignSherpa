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
| [open/](open/) | 1 | accepted, not started (the ISSUE-000 template is not counted) |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-001** — the pumice/granite microarchitecture is ASIC-shaped for an
  FPGA target: CAM lookup as the default, per-cycle recompute of storable facts,
  16 replicated FIFO controllers, storage arrays dissolved to flops by the async
  reset, same-cycle cross-plane cones, ASIC arithmetic, features the board cannot
  show a benefit for. pumice_core is 2.06x granite_core and holds only 50 MHz.
  Deep dive with measured costs and a ranked rework list. Owner direction
  2026-11-05. [open/ISSUE-001.md](open/ISSUE-001.md).
