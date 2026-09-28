# TASK-032: pumice placement pass: ddr2_char loose filelists (2) and 6 loose markdown files

**Priority:** P2
**Status:** open
**Owner:** pumice session (Sean pushes pumice from the workstation)
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists outside a `filelists/` dir (2 -- the pumice share of the baseline)

- `projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/rtl/ddr2_char_macro.f`
  and `rtl/chargen_regs.f` -> `rtl/filelists/`. Referrers: the `-f` line in
  `ddr2_char_macro.f` itself (pulls `chargen_regs.f`),
  `build-perf/rtl/filelists/ddr2_char_harness.f:16`,
  `ddr2-characterization/flows-litedram-uart/rtl/filelists/litedram_char_harness.f:21-23`,
  `ddr2_char_framework/dv/filelists/ddr2_char_macro_tb_top.f:4`,
  `ddr2_char_framework/dv/filelists/ddr2_char_uart_tb_top.f:13`, and the
  `bin/filelists.toml` comment at the `ddr2_char` area ("lives at the rtl
  root") which becomes wrong the moment they move.
- `pumice-ddr2-lpddr2/dv/tb/*_tb_top.f` were already moved to `dv/filelists/`
  by pumice TASK-009; nothing to do there.

## Markdown outside the book / known_issues / generated dirs (6, plus 2 at the family level)

Family level (`projects/components/memory-controllers/`): `ADVANCED_MODES_ROADMAP.md`
(a roadmap is a work list -- this lane), `DDR_FAMILY.md` (reader-facing family
overview; `README.md` beside it should link to it, not repeat it). pumice is the
only live member of the family, so these fall to this lane.


`projects/components/memory-controllers/pumice-ddr2-lpddr2/AT-A-GLANCE.md`
(status page), `dv/testplans/GAP_ANALYSIS.md`, and four micro-architecture
notes beside the RTL: `rtl/LPDDR2_CA_ENCODING.md`, `rtl/PUMICE_AXI4_IFC_UARCH.md`,
`rtl/PUMICE_DFI_LAYER_UARCH.md`, `rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md`. The
uarch notes are reader-facing design description: the MAS
(`docs/pumice_mas/`) is where a reader looks for them; if a chapter already
covers the same block, the beside-RTL copy is the second copy and goes.

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
