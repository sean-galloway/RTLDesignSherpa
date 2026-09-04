<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# cdc — task rollup

**Next ID: CDC-002** — never recycle a number, even when its task closed.

Canonical tracker for `rtl/cdc/` (`bin2gray`, `gray2bin`, the async FIFOs and
the pointer-synchroniser family), plus `val/cdc/` and
`docs/markdown/rtl-cdc/`.

Created 2026-09-04. The area had no tracker before -- CDC work was recorded in
whichever area happened to consume it, which is why the first task here is a
test scrub rather than a design item.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 1 | accepted, ready to start |
| [closed.md](closed.md) | 0 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Open

- **CDC-001** — scrub the tests for completeness. Part of the repo-wide test
  scrub that was meant to ride along with the kimi review packets and was
  dropped; run after qc/humanize, before coverage and formal are driven clean.
