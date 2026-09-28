# TASK-004: Project-area cleanup — apply the RTL-area pattern to projects/

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-010** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** deferred 2026-09-27 (state directory now matches the text; the gate is Sean's, 2026-07-24: "We will look into the projects once the RTL area is complete"). Re-open when Sean lifts the gate.
**Owner:** Sean (pumice push) / TBD

Once `rtl/` is clean (doc placement, CDC reorg, filelist consistency), apply the
same passes to `projects/`. "We will look into the projects once the RTL area is
complete" (Sean, 2026-07-24). This is the umbrella; each project below is a unit
of work.

**Per project, the same three passes done on rtl/common and rtl/amba:**
- doc placement ([[doc-placement]]): README → link, standalone guides →
  `docs/markdown/`, style guides/methodology → `vault/handbook/`, no PRD/spec
  docs loose in the tree. (README rollout is tracked broadly as DOCREV-007;
  this is the per-project execution.)
- filelist consistency ([[filelists]]): every `.f` in the owning dir's
  `filelists/`; a TB with its own harness gets its own filelist WITH the TB.
- verify `bin/filelist_registry.py --check` (all three counts) still resolves.

**Concrete known stragglers (from the 2026-07-24 survey):**
- [x] **bridge** — `rtl/filelists_static/` is JUSTIFIED, not a straggler (2026-09-27): `bin/filelists.toml`'s bridge area registers it with the reason -- `filelists/` is emitted by the generator and never hand-edited, `filelists_static/` holds the hand-written lists for the hand-written bridge RTL (`bridge_cam.f`); folding one into the other would put a hand-written file where `make regen` deletes.
- [ ] **rapids_char** (NexysA7) — `flows-rapids-beats/flists/` → `filelists/`
- [ ] **retro_legacy_blocks** — loose `rtl/rlb_top/rlb_top.f` → `filelists/`
      subdir. (`rtl/apbx_xbar/apbx_xbar_rlb_1to10.f` is gone: deleted
      2026-09-14 along with the hand-rolled crossbar it listed, which was
      replaced by the generated `apbx_xbar_1to10.sv`.)
- [ ] **ddr2_char** (NexysA7) — loose `rtl/ddr2_char_macro.f` → `filelists/`;
      the `dv/` harness `.f` get a `filelists/` dir WITH the TB
- [ ] **pumice** — `dv/tb/*_tb_top.f` → a `filelists/` dir with the TB.
      **PUMICE PUSHES FROM SEAN'S WORKSTATION, not this environment**
      (Sean, 2026-07-24) — make the pumice changes but do NOT push them; Sean
      pushes pumice from the workstation. See Tasks/pumice.
- [ ] the remaining components (converters, delta, hive, misc, apbx_xbar,
      dmas/{stream,rapids}, memory-controllers/{ddr3,ddr4}) get the same
      treatment as they are reached.

**Gate:** RTL area first (Tasks/INDEX.md sequencing). Do not start until the
cdc reorg + amba cleanup land.

---
