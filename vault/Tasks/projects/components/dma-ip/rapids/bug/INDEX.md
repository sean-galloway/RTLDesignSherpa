<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dma-ip/rapids — bugs

**Next ID: BUG-015** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 13 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Active


## Open


## Dropped

- **BUG-013** — WITHDRAWN AS WRONG the day it was filed. Claimed no data-path AXI
  monitor and that WRMON/RDMON configure nothing; both false. The monlites cover
  the data paths in BOTH trees and WRMON/RDMON configure them
  (`rapids_top.sv:1738` / `:1578`). Three greps that matched text rather than code
  produced it. See the file for the correction.

## Closed

- **BUG-014** — snk_data_path_axis channel-reset block clobbers a HEALTHY channel's
  same-cycle out-reg load / flush registration via stale `r_out_id`/`r_flush_ch`
  compares (silent data loss + PQ wedge). Found by the TASK-022 macro formal
  harness at BMC step 4; fix guarded both clears against a same-cycle load for
  another channel; the revert mutation re-caught at step 4; 822/822 byte-tree
  dv regression (closed 2026-10-02)
- **BUG-011** — two rapids formal proofs checked pre-BUG-009 RTL on stale sv2v flats; flats regenerated 2026-10-01, both proofs re-run PASS, the vacuity that let them pass filed as BUG-012. Self-detection fanned out to tooling TASK-026 (closed 2026-10-02)
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
