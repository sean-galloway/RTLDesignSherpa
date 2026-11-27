<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/onyx-ace-ccu — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 3 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **BUG-001** ([page](active/BUG-001.md)) — a killed upgrade's CleanUnique, snooped as MakeInvalid, dropped the stores of a peer that took the line Modified in between; now snooped CleanInvalid (IHI 0022). Found and fixed 2026-11-26 by the core-alone rig; closes on the proofs
- **BUG-002** ([page](active/BUG-002.md)) — a memory read could issue while a write to the same line was in flight on the memory port, returning pre-write bytes; the read now waits out the write port's burst to its line. Found and fixed 2026-11-26 by the core-alone rig; closes on the proofs
- **BUG-003** ([page](active/BUG-003.md)) — a stale write-back drain held behind a newer owner's absorption landed after it (a third requester needed: the IO port); an old write-back now goes first and the absorption waits for it. Found and fixed 2026-11-26 by the pair rig's full level; closes on the proofs

## Closed

(none)
