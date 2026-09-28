# TASK-004: Project-area cleanup — apply the RTL-area pattern to projects/

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-010** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-28 (gate lifted by Sean the same day: "do task 004, the RTL area is pretty complete at this point"). Global mechanism landed; per-unit remainder fanned out -- see the closing note.
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

---

## CLOSED 2026-09-28 -- what landed globally, what was fanned out

Sean's rule (2026-09-28): a tooling item is the GLOBAL mechanism only; anything
that needs edits inside several units is filed on each unit, or it never gets
done because every agent decides it is not wholly theirs. Applied here:

**Global (done in this item):**

- `bin/filelist_registry.py --placement`: every tracked `.f` must sit in a
  `filelists/` dir; `placement_ok` in `bin/filelists.toml` justifies a
  differently-named dir (bridge `filelists_static/`); ratcheted against
  `bin/filelist_placement_baseline.json` (8 known stragglers) and run in CI
  (`.github/workflows/filelist-checks.yml`). `--check` could not see a loose
  list (it still resolves) and `--blindspots` only asked whether the directory
  was registered, so this was the gap that let `rlb_top.f` sit loose for a year.
- The rule and the case recorded in [[filelists]].
- retro_legacy_blocks had no active owner, so its six moves were done here:
  `dv/tb/*_tb_top.f` (5) -> `dv/filelists/`, `rtl/rlb_top/rlb_top.f` ->
  `rtl/rlb_top/filelists/`; six tests, `retro_legacy_blocks_all.f`, the
  registry entry and `bin/check_port_consumers.py`'s comment repointed;
  `--check` / `--audit` PASS; RLB GATE 27/27 from `make clean-all`.
- Shared `projects/components/` doc placement: `COVERAGE.md` (described
  `make coverage-{all,fub,macro,top}` targets that no longer exist),
  `MAKEFILE_GUIDE.md` and `MAKEFILE_HIERARCHY.md` (dated 2025-10-24, describe
  the pre-TASK-009 Makefiles; `run-fub`, "48 workers", "~4 hours") and
  `PROJECT_QUICK_STATUS.md` (hand-maintained status, "Last Updated 2026-07-04",
  RLB at 15%) deleted -- each was a second copy of a handbook note
  ([[coverage]], [[running-regressions]]) or of the live tracker.
  `DOCUMENTATION_STANDARDS.md` retired in favour of [[spec-doc-standards]] plus
  `bin/DOC_GENERATION.md` (the caption numbering it carried is now in the note).
  `index.md` and `projects/README.md` repointed; `README.md` reduced to a link
  page per [[doc-placement]].

**Fanned out (one item per unit, each listing its own files):**

- rapids TASK-017 -- 3 `dv/tb/*.f` + Genesys2 `flists/` (the 6 rapids
  baseline entries) and 13 loose `.md`
- pumice TASK-032 -- ddr2_char `rtl/{ddr2_char_macro,chargen_regs}.f` (2
  baseline entries) and 8 loose `.md` (incl. the memory-controllers family pages)
- stream TASK-013 (9 `.md`), bridge TASK-012 (9 `.md`; `filelists_static/`
  justified), converters TASK-003 (2), misc TASK-004 (1), RLB TASK-016 (7 `.md`;
  filelists done here), asic-trials timing_characterization TASK-005 (3)
- apbx-xbar: nothing loose. delta and hive: retired 2026-09-27, no lane, their
  trees are left as they are.

The stragglers list above is superseded by the baseline file and the per-unit
items; the bridge line stays as the record of why `filelists_static/` is exempt.
