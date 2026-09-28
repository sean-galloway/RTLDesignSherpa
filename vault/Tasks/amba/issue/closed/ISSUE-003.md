# ISSUE-003: PKG-PAGES — CLOSED 2026-08-31: the premise did not survive measurement

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **AMBA-MONITOR** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Status:** CLOSED. Not by writing five pages -- by measuring what the five
actually were. The list came from "which .sv in includes/ has no same-named
.md", which is a filename test, not a coverage test. Measured with
word-boundary greps for `<pkg>::` (a substring grep is what made `apb5_pkg`
look alive -- it matches the generated `bridge_1x2_rw_apb5_pkg`):

| package | importers | outcome |
|---|---|---|
| `monitor_common_pkg` | **165** | already documented -- `monitor_package_spec.md` IS its page |
| `monitor_pkg` | **30** | already documented -- re-export shim, covered by that page's Backward Compatibility section |
| `apb4_pkg` | **1** (only `apb5_pkg`) | DELETED |
| `apb5_pkg` | **0** | DELETED |
| `axi_pkg` | **0** | DELETED |
| `bus_types.svh` | included by **0** | DELETED (it `include`d two of the above -- the only path that reached `axi_pkg`) |

So two needed no page and three were a vestigial type library. Writing pages
for them would have created three more documents to rot and lent legitimacy to
code nothing uses; `axi_pkg` was even listed in `amba_all.f`, so it compiled
into every area build while no module imported a single symbol.

Deleted the four files plus their references in `rtl/amba/filelists/amba_all.f`
and `formal/stream/stream_core/Makefile`. `index.md` now states positively that
`monitor_common_pkg` and `monitor_pkg` are documented under
`monitor_package_spec`, so the next audit does not re-raise this on a filename
search.

**Verified:** `amba_all.f` lints with 0 errors before and after; filelist
registry `--check` PASS; no dangling reference to any of the four anywhere in
`rtl/`, `formal/`, `projects/`, docs or generator templates.

**Found while verifying, and it is the bigger catch:**
`formal/stream/stream_core` had been flattening FIVE-WEEK-STALE monitor RTL.
Its prep pattern rule still sourced `rtl/amba/shared/%.sv` after the monitors
moved to `rtl/amba/monitor/` -- `MON_ORIG` was updated for the move, the
pattern rule was not. It never failed because the tracked `.sv2v_prep/*.sv`
snapshots satisfied make's dependency, so the broken rule never ran. Repointed
and regenerated; the flatten now tracks current RTL. That proof remains
DEFERRED for its own documented yosys `AST_AUTOWIRE` blocker -- it was not
passing before this and is not passing now, so nothing regressed. Recorded in
that directory's DEFERRED.md.

**Generalisable:** a checked-in generated artifact plus a broken rule that
would regenerate it is SILENT staleness. The artifact satisfies the
dependency, so the rule that would fail never runs. Only `make clean && make`
tests the rule. Same shape as the DEPS drift in [[TASK-025]].

---
