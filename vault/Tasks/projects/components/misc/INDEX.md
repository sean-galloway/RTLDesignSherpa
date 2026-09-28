<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# misc — task rollup

**Next ID: MISC-003** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 2 | 0 | 1 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../INDEX.md) for the full definitions.


Shared odds and ends under `projects/components/misc/`: the AXI4 interface
observers, the monbus tally/slave-monitor register blocks and
`dma_address_gen`.

Created 2026-09-04. The area had no tracker before.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 2 | 0 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

## Open shortlist

- **MISC-001** — move the three stray `.rdl` files out of `rtl/` into `rdl/`.
- **MISC-002** — scrub the tests for completeness (part of the repo-wide pass).
