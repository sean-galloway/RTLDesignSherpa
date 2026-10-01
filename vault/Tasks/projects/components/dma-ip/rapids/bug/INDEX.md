<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dma-ip/rapids — bugs

**Next ID: BUG-014** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 11 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **BUG-013** — no data-path AXI monitor, so an injected response error emits NO monbus packet (measured: 6 words captured, 0 error-class, only AXIS channel events); WRMON/RDMON read back their own writes while driving nothing (filed 2026-10-01)

- **BUG-011** — two rapids formal proofs (`axi_read_engine_beats`, `axi_write_engine_beats`) check pre-BUG-009 RTL: their sv2v flat snapshots were never regenerated; found by regenerate-and-diff (filed 2026-10-01)

## Closed

- **BUG-012** — the two engine proofs assumed the BUG-009 region away: `SCW=5` makes `XFER_MAX` exactly 15 and the assume capped the config AT 15, so the clamp could never engage and both flats proved identically. Assume widened, zero-beat input contract stated, `ap_*_len_within_alloc` added; now PASSES on the fixed RTL and FAILS on the pre-fix flat (closed 2026-10-01)

- **BUG-010** — top_beats axis_mon counted only completions, so a monitor's REPORTED dropped event (AXIS_ERR_EVENT_DROPPED) read as a lost packet; shared accounting helper, all three rapids TBs fixed, mutation-proved against a silent loss (closed 2026-10-01)

- **BUG-009** — a 256-beat burst (AxLEN 255) wrapped its size to 0 and poisoned the channel's SRAM bookkeeping; underneath it, whole-segment-only ingress allocation and a stale-view allocation race made a full-depth burst unsatisfiable -- CLOSED 2026-09-29 (three ILA-traced mechanisms, three ingress/engine fixes, board history replays clean on build 3)
- **BUG-001** — the board kick sequencer never writes KICK_ENABLE, and no sim can catch it
- **BUG-002** — the sink-ingress AXIS meter reads zero on hardware
- **BUG-003** — the source path stops 3-4 beats short of a long transfer and drains at 50%
- **BUG-004** — the read engine issues ARs against SRAM space it has already taken (closed 2026-09-27)
- **BUG-005** — the write engine runs two AWs per channel at PIPELINE=0 (closed 2026-09-27)
- **BUG-006** — the descriptor engine fetches any APB-kicked address, in range or not (closed 2026-09-27)
- **BUG-007** — a kick that ends in RD_ERROR wedges the channel's APB path through channel reset (closed 2026-09-27)
- **BUG-008** — the monitor PKT_MASK registers were documented as "1 = enable"; the hardware masks on 1 (closed 2026-09-28)
