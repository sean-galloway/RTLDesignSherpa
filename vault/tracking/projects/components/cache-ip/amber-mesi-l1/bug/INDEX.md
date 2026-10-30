<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/amber-mesi-l1 — bugs

**Next ID: BUG-005** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-004** — pend_eff repeat-snoop resolution drops a store (armed DOWNGRADE_S then READ_ONCE on an in-flight write-miss fill commits I; amber l1_control + jet_control share the defect; found by the jet FULL grid 2026-10-29).

## Active

(none)

## Closed

- **BUG-001** — miss_fill FULL soak txn 6040 (oracle miss + dirty-victim
  drain vs DUT hit): TB model bug, the BUG-002 stale-corpse eviction
  clobbering a live duplicate line's state. Masked at HEAD by the #106 RNG
  shift; proven and fixed via worktree at 7a3fe3000. Closed 2026-10-27.
- **BUG-002** — control FULL snoop soak 2126 (CRRESP IsShared vs 0): TB
  eviction accounting retired a live line through a dead {tag, I} corpse
  slot holding its stale tag; the DUT answered truthfully. Fixed by
  guarding the retire on the victim slot's pre-write validity (also
  `_replay_models` and monlite). Closed 2026-10-27.
- **BUG-003** — tally bins all zero on some seeds ("MonBus observation path
  is silent"): the path was never silent -- two stacked test-side bugs
  (CAM_LOAD VALID at bit 16 vs the regblock's bit 31, and write64's hi-word
  clobber through the tally's WSTRB-blind cfgw wrapper) emptied the legal-set
  CAM on every run; the seed flake was the smoke sweep reading bins with no
  freeze while the tally's registered readback leaked mid-RMW counts of the
  UNEXPECTED bin. Fixed test-side 2026-10-27; the wrapper wart filed as
  misc BUG-003.
