# TASK-003: converters placement pass: 2 loose analysis notes at the component root

**Priority:** P3
**Status:** CLOSED 2026-09-29 (done)
**Owner:** converters session
**Filed:** 2026-09-28 by tooling TASK-004 (fan-out)

## Filelists

None loose.

## Markdown outside the book (2)

`ANALYSIS_APB_CONVERTER.md`, `DUAL_BUFFER_IMPLEMENTATION.md` at the component
root. Both read as design analysis: fold into `docs/converter_mas/` where the
block chapter covers it, otherwise delete with the reason in the commit.

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

## CLOSED 2026-09-29 -- both notes gone; the one fact worth keeping is in the MAS

| File | Decision |
|---|---|
| `DUAL_BUFFER_IMPLEMENTATION.md` | **deleted.** It documented the `DUAL_BUFFER` ping-pong mode of `axi_data_dnsize`, which was removed from the RTL (`git log -S DUAL_BUFFER rtl/axi_data_dnsize.sv`, commit 7b50f2c3e); the MAS dnsize chapter already records the removal. 434 lines describing a feature that does not exist. |
| `ANALYSIS_APB_CONVERTER.md` | **deleted after folding.** Its conclusion -- keep `axi4_to_apb4_convert`'s inline width conversion rather than compose the generic blocks, and why -- was not in the MAS anywhere; it is now `docs/converter_mas/ch03_protocol_blocks/04_axi4_to_apb4.md` section 3.4.12 "Design Decision: Inline Width Conversion". The 300 lines of line-by-line comparison behind it are in git. |

README.md's "Available Documentation" list pointed at both, and at a
`rtl/GENERIC_MODULES_USAGE_GUIDE.md` that does not exist; it now points at
the MAS chapters and the two block specs under `docs/`.
