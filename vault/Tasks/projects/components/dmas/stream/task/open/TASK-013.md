# TASK-013: stream placement pass: 9 loose markdown files (status page, coverage and perf reports beside the tests)

**Priority:** P3
**Status:** open
**Owner:** stream session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists

None loose -- `--placement` lists nothing under stream.

## Markdown outside the book / known_issues / generated dirs (9)

`AT-A-GLANCE.md` (status page at the component root),
`coverage_combined/COMBINED_COVERAGE_SUMMARY.md`,
`dv/tbclasses/README_APB_CONFIG.md` (a how-to beside a TB class),
`dv/tests/combined_coverage/{combined_legal_report,combined_report_20260117_133736,combined_report_latest}.md`
(dated run output checked in as docs -- keep only what the coverage tooling
regenerates, and then only if something reads it),
`dv/tests/macro/perf_results/PERFORMANCE_SUMMARY.md`,
`dv/tests/macro/perf_results_realistic_sram/{FINAL_SUMMARY,REALISTIC_SRAM_ANALYSIS}.md`
(measurement write-ups -- the HAS performance chapter is the reader-facing home,
with the raw numbers left as artifacts).

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
