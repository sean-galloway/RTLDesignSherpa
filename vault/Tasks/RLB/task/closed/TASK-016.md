# TASK-016: RLB placement pass: 7 loose markdown files (status/roadmap/audit beside the RTL, a Makefile README beside the tests)

**Priority:** P3
**Status:** CLOSED 2026-09-28 -- all three criteria met; see the Outcome.
**Owner:** done
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

- [x] every file below has a decided home and is there (or is deleted with the
      reason in the commit message)
- [x] `python3 bin/filelist_registry.py --placement` lists nothing from this unit
- [x] the affected tests pass from `make clean-all`

## Outcome (2026-09-28)

Seven files, six moved or slimmed and one deleted. Paths above describe where
they WERE -- that is the record of what this task found, and is left standing.

| File | Home | Why |
|---|---|---|
| `rtl/RLB_STATUS_AND_ROADMAP.md` | `vault/Tasks/RLB/` | status/roadmap is a work item |
| `rtl/RLB_MODULE_AUDIT.md` | `vault/Tasks/RLB/` | an audit is a work item |
| `STRUCTURE_SETUP_SUMMARY.md` | `vault/Tasks/RLB/` | dated record of a one-time task; it says so itself, and closed TASK-007 cites it, so it is kept rather than deleted |
| `rtl/RLB_FPGA_IMPLEMENTATION_GUIDE.md` | `docs/` | reader-facing guide |
| `References/LegacyBlocksAndDriverGuide.md` | `docs/` | reader-facing; `References/` was an outlier no sibling component has, and it is now gone |
| `dv/tests/README_MAKEFILE.md` | slimmed 295 -> 24 lines | see below |
| `rdl/pm_acpi/pm_acpi_regs.md` | DELETED | see below |

**The Makefile README was NOT redundant for the reason this task gave.** The
task said "[[running-regressions]] is canonical". It is -- for METHOD. It does
not carry the per-block grammar (`run-apb4_hpet-gate`), the `-waves` suffix or
the utility targets that filled those 295 lines, and [[doc-placement]] rule 1
protects tool mechanics beside the tool. The real duplication is against
`make help`, which GENERATES the grammar from `make/tests.mk` and therefore
cannot drift -- while the page had already drifted, claiming 8 threads where
the area runs 48 workers. So it is a pointer at `make help` now, not a deletion.
Its per-block examples were all checked and DO resolve; an earlier probe of
mine called them dead, which was wrong (they are pattern rules, invisible to a
grep for an explicit target line).

**The pm_acpi markdown was a generated orphan.** `peakrdl_generate.py` writes
markdown to `<output_dir>/docs/<name>.md` (line 377); this copy sat directly in
`rdl/pm_acpi/`, outside any generated tree. `check_rdl_regen.py --list` shows
four pm_acpi manifest entries and none emits it, so nothing regenerated it and
nothing compared it -- the "orphan copy the build never reads, which then
drifts" that CLAUDE.md Rule #0 warns about. Deleted; git keeps the history. The
one row citing it (`rtl/pm_acpi/README.md`) was removed in the same commit.

**Referrers.** Three real markdown links in `docs/ioapic_mas/ioapic_mas_index.md`
and four inline-code references in `ch01_overview/{01_overview,05_references}.md`
were repointed, plus the audit's own cross-ref. The inline-code ones are
classified "inline-code" by the link checker and never validated, so their
silence proves nothing -- they were fixed for accuracy, not because a gate asked.

**Verified.** Broken links 3 -> 3 and the SAME three (all peer-owned: two
pumice MAS pages, one NexysA7 README), so no new break hides behind an
offsetting fix; `--ratchet` PASS, no file grew. `check_task_ids.py --area RLB`
passes with three status docs now at the lane root -- the position
`vault/Tasks/pumice-ddr2-lpddr2/GAP_ANALYSIS.md` already occupies. `check_rdl_regen.py`
in sync (silent on success; confirmed by reading main(), not assumed from a
clean exit). pm_acpi suite 6/6 from `clean-all`. A post-move sweep across all
file types found no stale reference outside this task file and a peer worktree.

**Two findings recorded, not acted on:**

- **No RLB block has its generated markdown checked.** Every RLB manifest entry
  carries `regmap_output: None` and no `.md` in `compare`, while STREAM, pumice,
  rapids, misc and the Genesys2/ddr2_char harnesses all compare a
  `generated/docs/<name>.md`. RLB simply does not emit docs markdown into a
  generated tree. Worth a task if that inconsistency is not deliberate.
- **`rtl/<block>/README.md` x10.** [[doc-placement]] rule 2 says no README under
  `rtl/` at all, but its case history is the top-level `rtl/` tree and it
  explicitly still permits READMEs in project areas. These were left alone
  rather than silently widening a 7-file task to 17.
