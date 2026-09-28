# TASK-002: Rehome NexysA7 under projects/fpga-systems + split Genesys2-specific flows

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Medium
**Status:** [ ] Open (2026-07-29)

**Goal:** Structural reorg of the FPGA board projects under the existing
`projects/fpga-systems/` parent.

**Moves:**
- Move `projects/NexysA7/` -> `projects/fpga-systems/NexysA7/`.
- The stream-perf / stream-mon collateral that is **Genesys2-specific** (today it
  lives under the NexysA7 tree, e.g. `flows-stream-bridge/rtl/stream_char_genesys2_top.sv`,
  `flows-stream-monitor/rtl/stream_mon_genesys2_top.sv`, and any Genesys2 XDC /
  build recipes) moves into a `projects/fpga-systems/Genesys2/` directory.
- Split shared vs board-specific: NexysA7-only tops/XDC stay under NexysA7,
  Genesys2-only under Genesys2, common harness/host under a shared area
  (mirrors the [[fpga/cmn-infra]] split already in the handbook).

**Then update ALL references:** filelists (`*.f`), `get_paths`/env roots in the
`dv/tests` wrappers, host `sys.path` inserts, Makefile paths, XDC includes, and
the handbook/vault links (`vault/handbook/fpga/NexysA7/...`,
`vault/handbook/fpga/Genesys2/...`, and this Tasks area's own path). Run
`bin/filelist_registry.py --check` and the char/mon sims after the move.

**Note:** likely rename/rehome this very Tasks area to
`vault/Tasks/projects/fpga-systems/...` (mirror-the-repo-path convention) as part
of the move; fold NEXYS-001 in with it.

---
