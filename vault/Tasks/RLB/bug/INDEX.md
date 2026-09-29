<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB — bugs

**Next ID: BUG-006** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 5 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open



## Closed

- **BUG-001** — regblock reset polarity composed by hand
- **BUG-002** — SYNCASYNCNET under -DRESET_ACTIVE_HIGH, family-wide
- **BUG-003** — an unmapped APB address hung the RLB bus
- **BUG-005** — the apb4_hpet example connected 9 nonexistent ports in PRD.md, README.md and rtl/apbx_xbar/README.md; fixed, and check_doc_examples.py widened to scan beside-code PRD/README, closed 2026-09-28.
- **BUG-004** — the PRD's address map was wrong four ways, not one: the base in eleven places, three shipped blocks (GPIO/UART/slave-PIC) documented as reserved, a nonexistent block at an unreachable window 0xF, and six "Planned" statuses for shipped blocks. Fixed in PRD.md and RLB_FPGA_IMPLEMENTATION_GUIDE.md; closed 2026-09-29.
