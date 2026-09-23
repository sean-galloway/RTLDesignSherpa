---
title: RAPIDS tasks
summary: Task rollup for the RAPIDS DMA component (projects/components/dmas/rapids).
---

# RAPIDS tasks

**Next ID: TASK-086** — never recycle a number, even when its task closed.

Task numbers are scoped to THIS area. The same number exists in other areas and that is expected, not a collision -- amba's TASK-080 and this one are different tasks, and the area is what tells them apart. Cite one as "RAPIDS TASK-080" when writing outside this file.

Task tracking for the RAPIDS (beats) DMA component, nested under
`projects/components/dmas/` to mirror the repo path. Lifecycle pages:
[open](open.md) · active · [closed](closed.md) · dropped (created when first needed).
Convention: [Tasks](../../../../INDEX.md).

## Open (not started)
- **TASK-057** — enforce register-map hygiene (port the STREAM lessons): use the
  by-name regmap, kick writes must prove descriptor fetches, no hand-added
  registers.
- **TASK-085** — backpressure runs record throughput numbers that cannot mean
  anything (the window shuts before the host can raise ready). Labelling, not RTL.

## Closed
- **TASK-081** — the board kick sequencer never wrote KICK_ENABLE. Fixed and
  board-confirmed 2026-09-22: 8 ch x 8 beats OVERALL PASS, AXI4-wr prod=64, all
  16 CRCs matching golden. See [closed](closed.md).
- **TASK-084** — one RTL harness: moved the host path (UART/CSRs/kick sequencer)
  down into `rapids_char_harness` so `verify-sim` reaches the launch path, per
  the STREAM shape. 104 ports -> 7; TB 738 -> 225 lines by reusing the board's
  own campaign. Re-validated sim + board, behaviour byte-identical.
- **TASK-083** — re-measured the beat-count knee: GONE. 28/28 board configs pass
  1..4096 beats at 8ch, including every point July 2026-07-15 failed.
- **TASK-082** — sink-ingress meter under-counted by min(dead_zone, total); gave
  `s_axis` its own window opened at ARM. Board-confirmed: shortfall 190 -> 0 at
  every size, other meters byte-identical.

The component's old `TASKS.md` / `rapids_beats_mas/TODO` next to the code are
still to be folded into this area per the one rule (no task files beside code).
