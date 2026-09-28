# TASK-029: move the last misplaced docs out of rtl/amba

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **AMBA-CLEANUP** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 (opened 2026-07-24)
**Priority:** P2

Both files resolved, though neither went where the task guessed — reading
them changed the destination, which is why the task said to read first:

- `rtl/amba/axi4/AXI4_DATA_WIDTH_CONVERTER_SPEC.md` — the dwidth converter
  RTL had itself MOVED to `projects/components/converters/` since this task
  was written, orphaning the spec from its module entirely. git mv'd to
  `projects/components/converters/docs/` (the component owns it; the
  converters MAS ch02_width_blocks is the maintained reader doc — whether
  the 1313-line original spec stays or folds into the MAS is the
  component's call). Both converter test `# Documentation:` headers
  repointed.
- `rtl/amba/VERIFICATION_ARCHITECTURE.md` — turned out to be a THIRD copy:
  its mandatory-requirements content is GLOBAL_REQUIREMENTS.md Category 2
  (the authority) and its guide content is
  `docs/user-guides/VERIFICATION_ARCHITECTURE_GUIDE.md` (675 lines,
  maintained). Deleted, referrers repointed to those two
  (root README table; the stale docstring example in
  `bin/review/make_meta_unit.py` — which never read the file, its
  `rtl/<area>/*.md` glob just swept it into review bundles).

Acceptance check passes: `find rtl/amba -name '*.md' | grep -v CLAUDE |
grep -v KNOWN_ISSUES` returns nothing. rtl/amba now has the same clean
shape as rtl/common.

---
