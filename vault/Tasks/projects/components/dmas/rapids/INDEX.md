---
title: RAPIDS tasks
summary: Task rollup for the RAPIDS DMA component (projects/components/dmas/rapids).
---

# RAPIDS tasks

**Next ID: TASK-082** — never recycle a number, even when its task closed.

Task numbers are scoped to THIS area. The same number exists in other areas and that is expected, not a collision -- amba's TASK-080 and this one are different tasks, and the area is what tells them apart. Cite one as "RAPIDS TASK-080" when writing outside this file.

Task tracking for the RAPIDS (beats) DMA component, nested under
`projects/components/dmas/` to mirror the repo path. Lifecycle pages:
[open](open.md) · active · closed · dropped (created when first needed).
Convention: [Tasks](../../../../INDEX.md).

## Open (not started)
- **TASK-057** — enforce register-map hygiene (port the STREAM lessons): use the
  by-name regmap, kick writes must prove descriptor fetches, no hand-added
  registers.

The component's old `TASKS.md` / `rapids_beats_mas/TODO` next to the code are
still to be folded into this area per the one rule (no task files beside code).
