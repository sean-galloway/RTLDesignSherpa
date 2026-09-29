# TASK-012: bridge placement pass: 9 loose markdown files (generator design notes beside bin/, a bug write-up at the root)

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
**Owner:** bridge session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists

`rtl/filelists_static/` is JUSTIFIED (registered with `placement_ok` in
`bin/filelists.toml`); `--placement` lists nothing under bridge.

## Markdown outside the book / known_issues / generated dirs (9)

Root: `BUG_APB_AXIL_FIFO_TRACKING.md` (a bug record -- belongs in this lane's
`bug/` dir or `known_issues/`), `GENERATOR_ARCHITECTURE.md`.
`bin/`: `BATCH_REGENERATION.md`, `BRIDGE_ID_TRACKING_DESIGN.md`,
`bridge_pkg/{SIGNAL_NAMING_INTEGRATION,SIGNAL_NAMING_QUICK_REF,SLAVE_ADAPTER_ADDITION}.md`.
The generator notes are the tool-mechanics case (Sean, 2026-09-25): mechanics
a reader of `bin/` needs may stay beside the generator, method that applies
everywhere goes to the handbook -- decide per file, and collapse the three
`bridge_pkg/` notes into one if they overlap.
`dv/testplans/COVERAGE_SUMMARY.md`, `dv/tests/README_TEST_EXECUTION.md`
(a how-to-run beside the tests; [[running-regressions]] is canonical).

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

---

## CLOSED 2026-09-29 -- nine files, each with a decided home

| File | Decision |
|---|---|
| `BUG_APB_AXIL_FIFO_TRACKING.md` (root) | -> **bridge BUG-015**, filed closed (resolved 2026-05-13); Sherpa doc header stripped, body kept |
| `GENERATOR_ARCHITECTURE.md` (root) | -> `bin/GENERATOR_ARCHITECTURE.md` (tool mechanics beside the tool). Build-flow and Makefile sections rewritten against `bin/Makefile` and `--help` (it described a `dv/tests/Makefile rebuild-all` that is now a four-line include, and YAML configs where the tree is TOML + CSV); the 2025-11 debugging journal (BUG-001) cut, 997 -> 674 lines; currency note added; remaining walkthroughs -> **bridge TASK-013**. Referrers fixed: `CLAUDE.md` x2, `PRD.md` x2, `dv/testplans/README.md` |
| `bin/BATCH_REGENERATION.md` | **deleted**: a 2025-11-10 one-time regeneration results snapshot; `bridge_batch.csv` + `make regen` are the mechanism, the lane is the record |
| `bin/BRIDGE_ID_TRACKING_DESIGN.md` | **deleted**: the implementation plan (steps, statuses) for the shipped ID tracking; the MAS `ch04_id_management` and `ch02/08_response_routing` describe the design |
| `bin/bridge_pkg/SIGNAL_NAMING_INTEGRATION.md` + `SIGNAL_NAMING_QUICK_REF.md` | **collapsed** into `bin/bridge_pkg/SIGNAL_NAMING.md`: both showed `cpu_m_axi_awid`-style names the module has not produced since TASK-011 and named functions that do not exist (`validate_signal_name`, `generate_master_ports`); the new page's API table is from the source and every example was executed |
| `bin/bridge_pkg/SLAVE_ADAPTER_ADDITION.md` | **deleted**: "Status: In Progress" plan from 2025-11-08 for `slave_adapter_generator.py`, which shipped |
| `dv/testplans/COVERAGE_SUMMARY.md` | **deleted**: a 2026-01-18 snapshot claiming `bridge_2x2_rw` cannot compile; the suite is 45/45 and coverage comes from `make coverage-report` |
| `dv/tests/README_TEST_EXECUTION.md` | **deleted**: a how-to-run whose central claim (parallel execution crashes the machine, run sequentially) contradicts the standing `run-all-*-parallel` practice; [[running-regressions]] is canonical, `make help` lists the targets, the markers are in `conftest.py` |

Gates after the pass: `check_broken_links --ratchet` PASS (3 outstanding,
none new), `check_doc_examples` 7 (unchanged), `filelist_registry
--placement` 0 stragglers, `check_task_ids` PASS. No `.f`, RTL or test file
moved, so no test was affected; none was run for this item.
