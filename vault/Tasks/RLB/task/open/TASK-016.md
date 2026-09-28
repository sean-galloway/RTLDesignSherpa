# TASK-016: RLB placement pass: 7 loose markdown files (status/roadmap/audit beside the RTL, a Makefile README beside the tests)

**Priority:** P3
**Status:** open
**Owner:** RLB session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists -- DONE by tooling TASK-004 (2026-09-28)

`dv/tb/*_tb_top.f` (5) -> `dv/filelists/`; `rtl/rlb_top/rlb_top.f` ->
`rtl/rlb_top/filelists/rlb_top.f`; six tests, `rtl/filelists/retro_legacy_blocks_all.f`
and the registry repointed; RLB GATE re-run from `make clean-all`. Nothing
loose remains under RLB.

## Markdown outside the book / known_issues / generated dirs (7)

`STRUCTURE_SETUP_SUMMARY.md` (root), `References/LegacyBlocksAndDriverGuide.md`
(reader-facing reference -- `docs/` or `docs/markdown/`), `dv/tests/README_MAKEFILE.md`
(the Makefile is four lines including `make/tests.mk`; [[running-regressions]]
is canonical), `rdl/pm_acpi/pm_acpi_regs.md` (check whether
`bin/peakrdl_generate.py` writes it -- if so it belongs under a `generated/`
dir, if not it is a stale hand copy), and three status/method pages beside the
RTL: `rtl/RLB_FPGA_IMPLEMENTATION_GUIDE.md`, `rtl/RLB_MODULE_AUDIT.md`,
`rtl/RLB_STATUS_AND_ROADMAP.md` (status and roadmap live in this lane).

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
