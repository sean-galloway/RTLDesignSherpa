---
title: Release status and post-1.0 change tracking
summary: Which areas reached v1.0 on 2026-10-06, and the rule that every later change to them is tracked with a GitHub issue.
---

# Release status and post-1.0 change tracking

The following areas reached **v1.0 on 2026-10-06**: every issue filed against
them is closed, the filed-issues list for each is empty, and the area is
considered feature-complete for its declared scope.

| Area | Repo path |
|---|---|
| Reed-Solomon | `projects/components/ecc-ip/reed-solomon` |
| Binary BCH | `projects/components/ecc-ip/bch` |
| STREAM DMA | `projects/components/dma-ip/stream` |
| RAPIDS beats (board characterization) | `projects/fpga-systems/Genesys2/dma-ip/rapids_beats` |
| RAPIDS | `projects/components/dma-ip/rapids` |
| APBx xbar | `projects/components/fabric-gen-ip/apbx-xbar` |
| bridge | `projects/components/fabric-gen-ip/bridge` |
| retro legacy blocks | `projects/components/retro_legacy_blocks` |
| rtl/common | `rtl/common` |
| rtl/cdc | `rtl/cdc` |
| rtl/math | `rtl/math` |
| amba apb4 | `rtl/amba/apb4` |
| amba apb5 | `rtl/amba/apb5` |
| amba axi4 | `rtl/amba/axi4` |
| amba axi5 | `rtl/amba/axi5` |
| amba axil4 | `rtl/amba/axil4` |
| amba axil5 | `rtl/amba/axil5` |
| amba axis4 | `rtl/amba/axis4` |
| amba axis5 | `rtl/amba/axis5` |
| amba gaxi | `rtl/amba/gaxi` |
| amba monitor | `rtl/amba/monitor` |
| amba shared | `rtl/amba/shared` |
| amba wb4 | `rtl/amba/wb4` |

The amba declaration is per sub-area: `rtl/amba/ace` is deliberately excluded
and is not at v1.0.

v1.0 is a statement about issue state and declared scope, not a promise that
the code cannot improve. RS keeps known open items (for example the erasure
`f = 2t` boundary, TASK-005) inside that scope boundary.

## The rule after 1.0

**Every change to a v1.0 area starts from a GitHub issue.** No drive-by
edits, no "while I was in there" refactors, no fixes landed without an issue
to file them against. The issue is the record of what was wrong, what was
decided, and what changed; the commit references it.

- Found a bug in a v1.0 area → file a bug issue, then fix.
- Want a feature or a revision bump → file a feature issue, then build.
- Touching the area for a repo-wide change → the repo-wide change's issue
  names the v1.0 area and why the touch is safe.

Areas not on the list above keep their current working practice; when an
area's last open issue closes, add it to the table here and the same rule
applies from that date.

## Why a rule

Pre-1.0, an area's issues *are* its roadmap and the work is "close them all."
Post-1.0, the work is "resist unrecorded change." An edit that nobody asked
for in an area everyone considers done is how a validated block quietly stops
being the block that was validated — the same failure the vault's mirror
layout exists to prevent, one directory up.

## See also

- [vault/Tasks/](../Tasks/INDEX.md) — vault task lifecycle; a vault task and a
  GitHub issue can reference each other, but the GitHub issue is the change
  tracker for v1.0 areas.
- [repo-wide-projects/](../repo-wide-projects/INDEX.md) — the per-area context
  notes; v1.0 areas are annotated there.
