<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# common — bugs

**Next ID: BUG-014** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 12 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-013** — non-FIFO reset bodies hardcoded active-low

## Closed

- **BUG-001** — ISSUE-001: counter.sv tick not gated during reset
- **BUG-002** — arbiter_round_robin_simple starved agents (Kimi round_2)
- **BUG-003** — RTL fixes surfaced by Kimi round_2 common review
- **BUG-004** — fifo_control default parameters contradict its own constraint
- **BUG-005** — shifter_beat_pack: runtime cfg wider than COUNT_BITS corrupts occupancy
- **BUG-006** — arbiter ACK mode: 105 unexpected ACKs, and the compliance model was muted
- **BUG-007** — the arbiter compliance model does not model block_arb
- **BUG-008** — simple arbiter "violations" are a monitor sampling bug
- **BUG-009** — ACK-mode arbiter compliance: the model loses a grant
- **BUG-010** — the fifo_sync wavedrom generator produces no wave JSON
- **BUG-011** — pwm formal prove FAILs: shadow model disagreed with the DUT
- **BUG-012** — FIFO-family reset bodies hardcoded active-low - FIXED
