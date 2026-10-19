<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/amber-mesi-l1 — bugs

**Next ID: BUG-003** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-001** — miss_fill FULL soak txn 6040: DUT serves a hit where the
  oracle expects miss + dirty-victim drain + fill. Deterministic seed 81795;
  pre-existing (reproduces at 255d8d9f5, 93ce944a2, HEAD). Found by FULL
  grid v2, 2026-10-12.
- **BUG-002** — control FULL snoop soak 2126: CRRESP IsShared set where the
  oracle expects 0. Deterministic seed 41099; pre-existing (reproduces at
  255d8d9f5, 93ce944a2, HEAD). Found by FULL grid v2, 2026-10-12.

## Active

(none)
