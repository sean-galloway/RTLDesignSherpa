# TASK-017: rapids placement pass: 6 loose filelists (dv/tb + Genesys2 flists/) and 13 loose markdown files

**Priority:** P2
**Status:** closed 2026-09-28 (closing note at the end)
**Owner:** rapids session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists outside a `filelists/` dir (6 -- all of the rapids share of the baseline)

- `projects/components/dma-ip/rapids/dv/tb/{alloc_ctrl,drain_ctrl,latency_bridge}_beats_tb_top.f`
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

- [x] every file below has a decided home and is there (or is deleted with the
      reason in the commit message)
- [x] `python3 bin/filelist_registry.py --placement` lists nothing from this unit
- [x] the affected tests pass from `make clean-all`

---

**CLOSED 2026-09-28.** Filelists: the three `dv/tb/*_beats_tb_top.f` moved to
`dv/filelists/` and `flows-rapids-beats/flists/` became `filelists/`; every
referrer repointed (the three fub_beats tests, `bin/filelists.toml` both
entries, `create_project.tcl`, `synth_only.tcl`, the two harness dv tests, the
`-f` lines inside the lists, the area README tree). `--check`, `--audit` PASS;
the placement baseline was rewritten to 0 stragglers. alloc_ctrl 120/120,
drain_ctrl 120/120, latency_bridge 81/81 at full from clean-all; the harness
dv tests pass on the moved lists.

Markdown, decided per [[doc-placement]]:

| File | Decision |
|---|---|
| `CONTROL_ENGINE_INTEGRATION.md` | staged plan / status tracker: moved to this lane's directory (`vault/Tasks/projects/components/dma-ip/rapids/`), like RLB's roadmap; 6 referrers repointed (2 RTL headers, 2 TB docstrings, 2 amba doc pages) |
| `RAPIDS_REFACTOR_PLAN.md` | superseded plan (executed as the beats architecture): moved beside it, for the "questions resolved" history |
| `docs/RAPIDS_Validation_Status_Report.md` | pre-beats status page: moved beside them; root and rapids PRD, CLAUDE.md and TASKS.md repointed |
| `bin/dma_model/OUTPUT_ORGANIZATION.md`, `docs/design_specification.md`, `docs/sram_insights.md` | tool mechanics and the model's own spec, referenced by the tool's README and `run_analysis.sh`: stay (doc-placement rule 1 exception) |
| `bin/dma_model/REORGANIZATION_SUMMARY.md`, `project_summary.md`, `docs/{complete_rw_analysis,rw_integration_summary,fixes_summary}.md` | work records of the model's own reorg and fixes (one opens "You're absolutely right"): deleted; the tree listing in OUTPUT_ORGANIZATION.md now names only the two docs that remain |
| `docs/ADDRESS_INCREMENT_PATTERNS.md` | reader-facing standalone analysis with its own PDF: stays at the component `docs/` root, the home RLB TASK-016 set for its two guides |
| `docs/rapids_specification_hive_context.md` | hive retired 2026-09-27: deleted |
| `docs/rapids_beats_mas/TODO.md` | every figure row DONE 2026-09-27 (TASK-010 holds the history): deleted; vault INDEX row updated |
| `dv/testplans/TESTPLAN_INDEX.md` | a second copy of the tables in `dv/testplans/README.md` (rule 3, one source per fact): deleted |
| `reports/AXIS_SRAM_OPTIMIZATION_ANALYSIS.md` | 2025 analysis of the retired pre-beats controllers, flagged historical since 2026-07-22: deleted |
| `rtl/signal_conflicts_report.md` | tool output: deleted; `bin/SIGNAL_NAMING_AUDIT.md` now says to generate one rather than pointing at a committed copy |

`bin/check_broken_links.py --ratchet` and `bin/check_task_ids.py` pass. Not in
scope and left alone: `TASKS.md` at the component root (the vault INDEX already
carries it as "still to fold in").
