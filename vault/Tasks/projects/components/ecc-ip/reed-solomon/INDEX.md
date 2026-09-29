# reed-solomon — task rollup

**Next ID: RS-002** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 2 | 0 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../../INDEX.md) for the full definitions.


Future `projects/components/ecc-ip/reed-solomon/` component. No RTL, DV or PRD
exists yet — this area holds the intent so it does not vanish when
COMMON-009 (BCH/Reed-Solomon ECC as library work) was dropped 2026-08-09.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

## Open shortlist

- **RS-001** — stand up the Reed-Solomon component (PRD first; scope decision
  BCH-in-or-out; own DV area). Waits on a real consumer.
