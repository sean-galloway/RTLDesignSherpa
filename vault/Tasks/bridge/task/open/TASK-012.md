# TASK-012: bridge placement pass: 9 loose markdown files (generator design notes beside bin/, a bug write-up at the root)

**Priority:** P3
**Status:** open
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
