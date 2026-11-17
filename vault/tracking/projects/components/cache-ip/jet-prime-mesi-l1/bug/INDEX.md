<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-prime-mesi-l1 — bugs

**Next ID: BUG-002** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what
correct looks like. If you cannot state the expected behaviour, it is an
ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **BUG-001** ([page](closed/BUG-001.md)) — the pipelined pair fabric presented
  its memory AR as a combinational lowest-index pick and re-pointed it at another
  slot during an `arready` stall (AXI A3.2.1); the hold that fixes it let a slot
  free in its AR's handshake cycle with the read outstanding. Both found by the
  fabric formal (TASK-001 step 4) and fixed 2026-11-17; the pair rig passed both.

## Dropped

(none)
