<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB — bugs

**Next ID: BUG-006** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-004** — PRD.md gives the subsystem base as 0x4000_0000 in three places; the RTL uses BASE_ADDR 0xFEC00000, which the PRD never mentions.

## Closed

- **BUG-001** — regblock reset polarity composed by hand
- **BUG-002** — SYNCASYNCNET under -DRESET_ACTIVE_HIGH, family-wide
- **BUG-003** — an unmapped APB address hung the RLB bus
- **BUG-005** — the apb4_hpet example connected 9 nonexistent ports in PRD.md, README.md and rtl/apbx_xbar/README.md; fixed, and check_doc_examples.py widened to scan beside-code PRD/README, closed 2026-09-28.
