# reed-solomon — task rollup

**Next ID: TASK-004** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 0 | 2 | 0 | 1 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../../INDEX.md) for the full definitions.

This rollup carried a second, duplicated count table and the line "No RTL, DV
or PRD exists yet" from when the area was a placeholder. Both are removed: the
component has RTL, a 246-test DV area and four validated board images. The
counts above now match the directories.

## Open shortlist

Nothing open right now — the component is at a clean stopping point.

- **TASK-003** (deferred) — first consumer selection (PRD D10), pending a
  memory controller project consumer (Sean's direction, 2026-10-02).

Closed history:

- **TASK-001** (CLOSED 2026-10-02) — the stand-up umbrella: codec, both
  solvers, wrappers, DV area, HAS and the board harness all exist and pass.
  Closed with D4 decided (both shapes viable) and the two successors above.
- **TASK-002** (CLOSED 2026-10-03) — erasure decoding (PRD D5): the
  errors-plus-erasures path, model-first, both solvers, DV matrix, injector
  erasure mode. Closed with all six phases landed: gate 102/102 and the
  harness cosim 17/17 green at close.
