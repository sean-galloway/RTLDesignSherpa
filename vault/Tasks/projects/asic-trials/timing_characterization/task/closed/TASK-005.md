# TASK-005: timing_characterization placement pass: 3 loose how-to guides

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
**Owner:** asic-trials session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists

None loose (`char_top.f` sits in a `filelists/` dir).

## Markdown outside the book (3)

`README_FPGA.md`, `RTL_TO_ASAP7_OSS_FLOW.md` (root), `rtl/syn/SYNTHESIS_GUIDE.md`.
Flow how-tos: the process goes to `vault/handbook/fpga/` (or the ASIC
equivalent), the area README stays a link page.

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

## CLOSED 2026-09-29 -- one file moved, two stay for stated reasons

| File | Decision |
|---|---|
| `RTL_TO_ASAP7_OSS_FLOW.md` | -> `vault/handbook/asic/rtl-to-asap7-oss-flow.md`. A toolchain how-to is method; the handbook had no ASIC area, so `vault/handbook/asic/` (INDEX + this note) is new and listed in the handbook root INDEX. Pointers added to this area's `README.md` docs list and `CLAUDE.md`. |
| `README_FPGA.md` | **stays.** It is not a how-to; it is the SOURCE of the FPGA companion white paper (`docs/generate_wp_fpga_pdf.sh` reads `../README_FPGA.md` through md_to_docx), exactly as `README.md` is the ASIC paper's source. A file the tooling reads stays where the tooling expects it ([[doc-placement]] rule 5). |
| `rtl/syn/SYNTHESIS_GUIDE.md` | **stays.** Tool mechanics beside the tool (the SDC parameters, per-flow setup, per-FUB recipes a reader of `rtl/syn/` needs -- the 2026-09-25 exception), referenced from the HAS and MAS indexes, `PRD.md` and `CLAUDE.md`. |

`filelist_registry --placement` had nothing here before and has nothing now.
