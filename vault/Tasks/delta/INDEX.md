# delta — task rollup

**Next ID: DELTA-011** — never recycle a number, even when its task closed.

Area for the Delta AXI-Stream crossbar generator
(`projects/components/fabric-gen-ip/delta/`). Re-homed from `noc-ip/` on
2026-10-12 (tooling TASK-031); the aspirational DELTA mesh NoC draft it once
carried lives separately at `projects/components/noc-ip/delta_spec/` and is
NOT tracked here.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`,
`deferred/`). Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 3 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.
