<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/utility-ip/misc — bugs

**Next ID: BUG-003** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-002** — the observers' compression statistics nets (`w_comp_stat_*`) are declared and
  read into OBS_COMP_STAT0/1 but never driven; the CSRs read 0 on every build (filed 2026-10-24)

## Closed

- **BUG-001** — error_injector CLUSTERS mismatch on SEED=33472: stale draw-walk
  done released the block-start beat one cycle early; closed 2026-10-16
