# TASK-032: CONSISTENCY — normalize where .f lists live

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **AMBA-FILELIST** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** Closed 2026-09-15 -- verified; the remaining work is TOOL-010's.
Was: open 2026-07-24 — **the RTL-area filelists are already consistent; the actual stragglers are all under projects/ and moved to TOOL-010.** This entry is kept only to record that rtl/amba, rtl/common, rtl/math are clean.
**Priority:** P3

The convention (see [[filelists]]) is: a module's `.f` lives in the owning
area's **`filelists/` dir**, and `bin/filelists.toml` REGISTERS it (the toml is
an index, not storage). Most of the 366 `.f` follow this
(`rtl/amba/filelists/` 118, `rtl/common/filelists/` 56, `rtl/math/filelists/`
38). Sean, 2026-07-24: right now placement is inconsistent. The stragglers:

**Naming -- not called `filelists/`:**
- [ ] `projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/flists/`
      (3 files) -> `filelists/`
- [ ] `projects/components/bridge/rtl/filelists_static/` -> fold into
      `filelists/` (or justify why "static" is a distinct dir)

**Loose `.f` directly beside RTL, no `filelists/` subdir:**
- [ ] `projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.f`
- [ ] `projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/ddr2_char_macro.f`

**TB/harness `.f` -- RESOLVED (Sean, 2026-07-24):** a testbench with its own
harness gets its own filelist, co-located WITH the TB (its `filelists/` dir),
not with the RTL. So `*_tb_top.f` under `dv/` are correctly placed in principle;
they just need the same `filelists/`-dir naming. `val/amba/filelists/
monbus_arbiter_grant_hold_dut.f` is a TB list and stays with its TB.

**SCOPE / SEQUENCING (Sean, 2026-07-24):** the RTL-area filelists are ALREADY
consistent -- `rtl/amba/`, `rtl/common/`, `rtl/math/` all use `filelists/`. Every
straggler above is under `projects/` (or a project's `val/`). **Projects are
deferred until the RTL area is complete.** So this task does not start now; it
waits behind the RTL-area work (cdc reorg, amba cleanup). Re-check with
`bin/filelist_registry.py --check` when it runs.

---


**CLOSED 2026-09-15 — both claims verified, and the work it points at lives
elsewhere.** This entry had already reduced itself to a record: it says the
RTL-area filelists are consistent and the real stragglers moved to
[[TOOL-010]]. Re-measured rather than taken on trust:

* every RTL area uses a `filelists/` dir and has **zero** loose `.f` beside
  the RTL -- `rtl/amba` 165, `rtl/math` 173, `rtl/common` 49, `rtl/cdc` 16.
* all four listed stragglers still exist and all four are under `projects/`:
  `flows-rapids-beats/flists/`, `bridge/rtl/filelists_static/`,
  `retro_legacy_blocks/rtl/rlb_top/rlb_top.f` and
  `NexysA7/.../ddr2_char_macro.f`.
* TOOL-010, which owns them, is still open in the tooling tracker.

So nothing here is actionable in amba: the RTL side is done, and the
projects side is TOOL-010's, deferred behind the RTL-area work by Sean's own
sequencing note. Keeping it open in amba only made the area look busier than
it is.

---
