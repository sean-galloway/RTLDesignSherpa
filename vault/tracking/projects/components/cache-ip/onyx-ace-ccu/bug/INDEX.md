<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/onyx-ace-ccu — bugs

**Next ID: BUG-007** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-004** ([page](open/BUG-004.md)) — the grant's rotating pointer plus the per-line lock can starve a requester on a contended line (an IO polling a line overtakes cache 0 without bound). Found 2026-11-27 by the liveness harness (L1b)
- **BUG-005** ([page](open/BUG-005.md)) — two yielding same-line write-backs can block each other forever at the write port (`r_aw_yield` re-arms while any same-line AW is presented); N >= 3, or N = 2 with back-to-back same-line AWs. Found 2026-11-27 by the liveness harness (L4.yield)
- **BUG-006** ([page](open/BUG-006.md)) — a replay can starve behind its requester's streaming memory beats (`r_rpl_hold` arms only after a refused replay beat). Found 2026-11-27 by the liveness harness (L2.rpl)

## Active

(none)

## Closed

- **BUG-001** ([page](closed/BUG-001.md)) — a killed upgrade's CleanUnique, snooped as MakeInvalid, dropped the stores of a peer that took the line Modified in between; now snooped CleanInvalid (IHI 0022). Found and fixed 2026-11-26 by the core-alone rig; closed 2026-11-27 on the proofs (`prove` and `prove_book` PASS on the fixed flat)
- **BUG-002** ([page](closed/BUG-002.md)) — a memory read could issue while a write to the same line was in flight on the memory port, returning pre-write bytes; the read now waits out the write port's burst to its line. Found and fixed 2026-11-26 by the core-alone rig; closed 2026-11-27 on the proofs (`prove` and `prove_book` PASS on the fixed flat)
- **BUG-003** ([page](closed/BUG-003.md)) — a stale write-back drain held behind a newer owner's absorption landed after it (a third requester needed: the IO port); an old write-back now goes first and the absorption waits for it. Found and fixed 2026-11-26 by the pair rig's full level; closed 2026-11-27 on the proofs (`prove` and `prove_book` PASS on the fixed flat)
