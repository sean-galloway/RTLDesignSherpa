<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# cdc — task rollup

**Next ID: CDC-005** — never recycle a number, even when its task closed.

Canonical tracker for `rtl/cdc/` (`bin2gray`, `gray2bin`, the async FIFOs and
the pointer-synchroniser family), plus `val/cdc/` and
`docs/markdown/rtl-cdc/`.

Created 2026-09-04. The area had no tracker before -- CDC work was recorded in
whichever area happened to consume it, which is why the first task here is a
test scrub rather than a design item.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 0 | accepted, ready to start |
| [closed.md](closed.md) | 5 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Open

Nothing open -- all five tasks are closed; see [closed.md](closed.md). (CDC-001
was listed here as open after it had already closed, which is the stale-index
pattern this area keeps hitting: the work lands, the closed page is updated,
and the open page keeps advertising it.)
