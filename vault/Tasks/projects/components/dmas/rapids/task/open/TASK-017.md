# TASK-017: rapids placement pass: 6 loose filelists (dv/tb + Genesys2 flists/) and 13 loose markdown files

**Priority:** P2
**Status:** open
**Owner:** rapids session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists outside a `filelists/` dir (6 -- all of the rapids share of the baseline)

- `projects/components/dmas/rapids/dv/tb/{alloc_ctrl,drain_ctrl,latency_bridge}_beats_tb_top.f`
  -> `dv/filelists/` (the TB `.sv` stays in `dv/tb/`). Referrers:
  `dv/tests/fub_beats/test_{alloc_ctrl,drain_ctrl,latency_bridge}_beats.py`
  (`filelist_path=`), and `bin/filelists.toml` rapids `filelist_dirs`
  (`.../dv/tb` -> `.../dv/filelists`).
- `projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/flists/{rapids_char_genesys2_top,rapids_char_harness,rapids_char_top}.f`
  -> `flows-rapids-beats/filelists/`. Referrers: `tcl/create_project.tcl:140`
  (`$project_root/flists/`), `tcl/synth_only.tcl` header comment,
  `dv/test_rapids_char_harness.py`, `dv/test_rapids_char_top_kick.py`, the
  `-f` lines inside the lists themselves, the area `README.md` tree, and
  `bin/filelists.toml` `genesys2_rapids_beats_char` `filelist_dirs`.

## Markdown outside the book / known_issues / generated dirs (13)

Component root: `CONTROL_ENGINE_INTEGRATION.md`, `RAPIDS_REFACTOR_PLAN.md`.
`bin/dma_model/`: `OUTPUT_ORGANIZATION.md`, `REORGANIZATION_SUMMARY.md`,
`project_summary.md`, `docs/{complete_rw_analysis,design_specification,fixes_summary,rw_integration_summary,sram_insights}.md`.
`docs/`: `RAPIDS_Validation_Status_Report.md`, `ADDRESS_INCREMENT_PATTERNS.md`,
`rapids_specification_hive_context.md` (hive was retired 2026-09-27),
`rapids_beats_mas/TODO.md` (a work list inside a book).
`dv/testplans/TESTPLAN_INDEX.md`, `reports/AXIS_SRAM_OPTIMIZATION_ANALYSIS.md`,
`rtl/signal_conflicts_report.md` (tool output -- regenerate or drop).

## Why this is filed here and not on tooling

Tooling TASK-004 (project-area cleanup) closed 2026-09-28 with the GLOBAL
mechanism in place: `bin/filelist_registry.py --placement` (ratcheted in CI,
baseline `bin/filelist_placement_baseline.json`) and the placement rules in
[[filelists]] and [[doc-placement]]. Per Sean (2026-09-28): an item that needs
edits inside many separate units is filed on each unit, or it never completes.
This is the per-unit share; nobody outside this unit will do it.

## Rules to apply (do not restate them here -- the notes are canonical)

- [[doc-placement]]: method/practice -> `vault/handbook/`; reader-facing
  pages -> this component's `docs/` book or `docs/markdown/`; work items,
  status pages, plans and "summary" files -> `vault/Tasks/<lane>/` (or delete
  when stale -- git keeps the history); a file the tooling READS stays put;
  beside-code `CLAUDE.md` / `PRD.md` / `README.md` stay, and a README is a
  link page, never a second copy of the spec.
- [[filelists]]: every `.f` in the owning dir's `filelists/` subdir
  (`rtl/<block>/filelists/`, `dv/filelists/` for a TB wrapper). After moving
  one, update every referrer (`filelist_path=`, tcl, README trees,
  `bin/filelists.toml` `filelist_dirs`), run `python3 bin/filelist_registry.py
  --check --audit`, then `--placement --update-placement-baseline` so the
  ratchet shrinks, and re-run the affected tests from `make clean-all`.

## Done when

- [ ] every file below has a decided home and is there (or is deleted with the
      reason in the commit message)
- [ ] `python3 bin/filelist_registry.py --placement` lists nothing from this unit
- [ ] the affected tests pass from `make clean-all`
