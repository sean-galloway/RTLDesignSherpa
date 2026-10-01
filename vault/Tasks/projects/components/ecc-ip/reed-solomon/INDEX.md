# reed-solomon — task rollup

**Next ID: RS-002** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 1 | 0 | 0 | 0 |
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

- **TASK-001** (ACTIVE) — stand up the Reed-Solomon component. Largely done and
  worth a status decision: the codec, both solvers, the AXIS and AXI4 wrappers,
  the DV area and the Nexys A7 loop harness all exist and pass. What the item
  still names and does not have is a PRD-level scope decision (BCH in or out)
  and a real consumer. Close it and file what remains, or keep it open as the
  umbrella -- an owner's call, not a mechanical one.
