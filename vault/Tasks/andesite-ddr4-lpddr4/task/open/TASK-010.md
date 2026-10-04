# TASK-010: BFM DFI 4.0 gap closure (G1-G5)
> Source: andesite TASK-005 study, 2026-10-04; gaps recorded in andesite HAS
> ch06 (`docs/andesite_has/ch06_integration/01_verification_open.md`)
> Work lands in the DV repo: `/mnt/data/github/RTLDesignSherpa-DV/src/CocoTBFramework/components/dfi/`

**Priority:** P2
**Status:** open 2026-10-04
**Owner:** TBD

Close the five gaps the TASK-005 study found between the andesite verification
strategy and the in-house BFM's DFI 4.0 coverage. Work is in the DV repo;
this task tracks it from the consumer side.

- [ ] **G1** — LPDDR4 6-bit CA command map: no `lpddr4_ca_map.py`;
  `ca_map.py` ships HBM4 and DDR5 maps only, and `lpddr_ca.py` is LPDDR2-only.
  Blocks MAS CA-submodule verification and the HAS ch06 item-6 checker.
- [ ] **G2** — Design-point JEDEC timing CSVs: no `ddr4-1600.csv`, no LPDDR4
  CSV (`jedec/` carries 2400/2666/3200). The design point is DDR4-1600 /
  LPDDR4-1600.
- [ ] **G3** — Gear-down behavior: `dfi_geardown_en` is in the signal catalog
  but `DFIv4_0Behavior` has no geardown sampling method (HAS Q3's coverage
  question rides on this).
- [ ] **G4** — LPDDR4 CA-VREF training: `dfi_calvl_data`/`done`/`result`/
  `strobe` unmodeled; `training_step()` inherits v3.1 CA-training detection.
- [ ] **G5** — Per-slice read leveling: all `TrainingEvent`s return
  `slice_idx=0`; DFI 4.0 makes `rdlvl_*` per-slice.

Closes when all five land in the DV repo with tests, and andesite HAS ch06's
gap table is marked closed (each row annotated with the commit that fixed it).
