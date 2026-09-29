<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dmas/rapids — bugs

**Next ID: BUG-010** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 8 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-009** — the sink wedges when a write burst equals the per-channel SRAM depth (WR_XFER_BEATS = SRAM_DEPTH - 1); found on the Genesys 2, single-channel knob sweep 2026-09-29


## Closed

- **BUG-001** — the board kick sequencer never writes KICK_ENABLE, and no sim can catch it
- **BUG-002** — the sink-ingress AXIS meter reads zero on hardware
- **BUG-003** — the source path stops 3-4 beats short of a long transfer and drains at 50%
- **BUG-004** — the read engine issues ARs against SRAM space it has already taken (closed 2026-09-27)
- **BUG-005** — the write engine runs two AWs per channel at PIPELINE=0 (closed 2026-09-27)
- **BUG-006** — the descriptor engine fetches any APB-kicked address, in range or not (closed 2026-09-27)
- **BUG-007** — a kick that ends in RD_ERROR wedges the channel's APB path through channel reset (closed 2026-09-27)
- **BUG-008** — the monitor PKT_MASK registers were documented as "1 = enable"; the hardware masks on 1 (closed 2026-09-28)
