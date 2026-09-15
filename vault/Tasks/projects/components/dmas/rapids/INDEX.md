---
title: RAPIDS tasks
summary: Task rollup for the RAPIDS DMA component (projects/components/dmas/rapids).
---

# RAPIDS tasks

**Next ID: RAPIDS-001** — never recycle a number, even when its task closed.

This area's older entries use the bare `TASK-` prefix, which is amba's namespace -- `TASK-080` names one task here and a DIFFERENT one in STREAM. New IDs take the `RAPIDS-` prefix so the collision cannot grow; the existing `TASK-` entries are left alone pending a decision, since renaming them moves live wikilinks. Numbering starts at 001: the PREFIX already disambiguates, so RAPIDS-001 cannot be confused with TASK-057, and starting high would invent 80 phantom gaps in the ID sequence.

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
