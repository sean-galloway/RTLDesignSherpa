<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-prime-mesi-l1 — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what
correct looks like. If you cannot state the expected behaviour, it is an
ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **BUG-002** ([page](active/BUG-002.md)) — a write-back victim passed on by a
  snoop still drained, and its stale bytes could land after the new owner's
  write-back (two caches, no IO port; found as onyx ISSUE-002, reproduced
  2026-11-24 by a hot-set soak phase). Fixed and sim-verified 2026-11-24: the
  entry ends at the snoop, a draining one answers no further snoop, the
  fabric orders same-line write-backs by presentation; proofs running.

## Closed

- **BUG-003** ([page](closed/BUG-003.md)) — the fill unit test's capture-hold
  check summed the beats of the slot behind the held one, which the
  out-of-order responder may legitimately stream (seed 13525); split per
  slot 2026-11-24.
- **BUG-001** ([page](closed/BUG-001.md)) — the pipelined pair fabric presented
  its memory AR as a combinational lowest-index pick and re-pointed it at another
  slot during an `arready` stall (AXI A3.2.1); the hold that fixes it let a slot
  free in its AR's handshake cycle with the read outstanding. Both found by the
  fabric formal (TASK-001 step 4) and fixed 2026-11-17; the pair rig passed both.

## Dropped

(none)
