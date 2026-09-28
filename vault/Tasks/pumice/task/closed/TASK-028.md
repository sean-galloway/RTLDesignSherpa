# TASK-028: real K-maps for the scheduler, CAMs and DFI layer

> **Migrated from `PUMICE-KMAP`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-KMAP` reference resolves. Body below is verbatim from the flat page.
>
> **This item was MISSED by the first pass of the migration** and added after a
> peer session's independent count came to 36 where mine said 35. The parser
> matched `PUMICE-\d+`, which requires digits, so the one ID in this area whose
> suffix is a WORD rather than a number was skipped silently -- and the
> assertion meant to catch that (`expect 35`) had been derived from the same
> parser's own output, so it confirmed the wrong assumption instead of
> contradicting it. An expected count has to come from the source, not from the
> tool being checked.


**Status:** CLOSED 2026-09-10  **Was blocked on:** [[TOOLING-KMAP]] items 1-4

All six criteria of [[signal-contracts-and-kmaps]] are discharged across the 17
computed maps, the artifacts are consolidated, and both halves are gated so they
cannot silently rot again.

**One workbook, one generator.** Four workbooks from three generators across two
directories became `docs/pumice_signal_contracts.xlsx` from
`docs/gen_pumice_signal_contracts.py`, verified to reproduce all 18 original
sheets cell-for-cell. The old flow LOADED the workbook and appended rows, so
re-running duplicated them (the committed Scheduler sheet had 8 such rows); the
new one builds from scratch and is idempotent. An INDEX sheet separates SPEC
tables from COMPUTED grids and opens with the measured RTL status, so the book
cannot be read as a bug list for a controller that meets its targets.

**Criterion 1 (computed, not drawn) was FALSE for four maps**, now gated.
`rd_col_m`/`wr_col_m` modelled 7 terms against 13; `w_ref_safe`, `w_guarded`,
`w_drain_active` each dropped one. `docs/check_kmap_rtl_sync.py` requires every
RTL identifier on a signal's RHS to be NAMED in the documented expression (folds
stay legal, the fold equation is in [brackets]). **16 of 17 machine-checked, 0
drifted**; the generator REFUSES to write on drift.

**Criteria 3/4/5/6.** Axis-term tables with file:line on the four maps whose axes
are folds; relations on all 17 (constraint or explicit independence note); 38
don't-care cells from cited invariants; Quine-McCluskey implicants printed beside
the documented equation on every map.

**Waves: audited, corrected, extended, RENDERED, in the MAS.** The set was drawn
at tCCD=2 with streams captioned "~100% util" -- impossible, and the RTL settles
it (BURST_WORDS=1, so a column every cycle, which is the measured 571.3 MB/s).
Added seven performance diagrams: 13-17 bad-but-correct (admit gate, ring bound,
page thrash, turnaround thrash, refresh storm) and 18-19 pathological, each
captioned with the board number it produced. `design/check_waves.py` found **11
real defects** in the pre-existing diagrams, five of them labels attached to a
logic level instead of a bus slot (WaveDrom silently shifts every label in the
row onto the wrong segment). `design/render_waves.py` produces SVG+PNG for all
19 and **MAS Chapter 7** embeds every one. Rendering itself exposed that every
caption (101-431 chars) overflowed the image and 23 group labels overlapped --
neither visible in the JSON, neither ever seen because nothing had been rendered.

**The lesson.** A spec written during a debugging campaign dates instantly and
silently: these artifacts asserted a 15%-of-peak controller and five live
defects while the board ran at 95% in both directions. Mechanical checks, not
review, are what keep hand-built collateral honest -- every check added here
failed on its first run.

---
