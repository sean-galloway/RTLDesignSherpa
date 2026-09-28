<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# cdc — task rollup

**Next ID: CDC-005** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 2 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 3 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.


Canonical tracker for `rtl/cdc/` (`bin2gray`, `gray2bin`, the async FIFOs and
the pointer-synchroniser family), plus `val/cdc/` and
`docs/markdown/rtl-cdc/`.

Created 2026-09-04. The area had no tracker before -- CDC work was recorded in
whichever area happened to consume it, which is why the first task here is a
test scrub rather than a design item.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 0 | 0 | 2 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 3 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

## Open

Nothing open -- all five tasks are closed; see the closed/ dirs (CDC-001
was listed here as open after it had already closed, which is the stale-index
pattern this area keeps hitting: the work lands, the closed page is updated,
and the open page keeps advertising it.)
