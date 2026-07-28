<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# site-audit — open

## AUDIT-001 — Site-wide audit: RTL correct, docs match, docs humanized, verification covers it
**Status:** open 2026-07-28 — scope clarifying as it goes; expect a split into per-part children
**Priority:** P1
**Owner:** Sean / TBD

One umbrella sweep over the whole repo, four parts. Run it area by area
(rtl/common, rtl/math, rtl/amba, then projects/) so a bad area is contained;
an area is only "audited" when all four parts have evidence on file for it.

### Part 1 — the RTL itself is correct

The RTL has had heavy validation already, so the expectation is FEW issues —
a large findings count here is itself a signal that the method is wrong, not
that the RTL is suddenly bad.

- [ ] All regressions green at FULL level per area
      ([[running-regressions]] — `make clean-all && make run-all-full-parallel`,
      never bare pytest).
- [ ] Formal proofs pass where they exist; gaps recorded for Part 4
      ([[formal]]).
- [ ] External correctness critique per area (Kimi `qc` rounds already
      surface RTL defects, not just doc bugs — triage each CONFIRMED finding
      as RTL-vs-doc, per [[kimi-review-rounds]]). Findings become tasks in
      the OWNING area (amba/common/pumice/RLB), not here.

### Part 2 — docs/markdown/* matches the RTL

This is the correctness half of DOCREV-009, promoted: every `.md` in the
area (index/readme/overview/quickstart + per-module pages) checked against
the CURRENT tree, including the meta-docs where count/structure drift hides
(the rtl/common 86-vs-55 case). Confirmed mismatches become DOCREV work.

- [ ] Per-area correctness pass, measured against the tree.
- [ ] Broken links fixed (DOCREV-011); every book has index.md +
      overview.md (DOCREV-010).

### Part 3 — humanize the docs

Per `docs/kimi_humanization_style_guide.md` and [[humanization-voice]].
Correctness FIRST, voice second — never humanize a doc that is known-wrong
(the voice pass must not "improve" bad content). Covers ALL md, not just
prose docs: index, readme, overview, module pages.

- [ ] Per-area humanization pass after that area's Part 2 is clean.

### Part 4 — verification has excellent coverage

TB quality, coverage metrics, formal — per area:

- [ ] Line/toggle coverage measured and the gaps triaged
      ([[coverage]]; the `val/COVERAGE_TODO.md` backlog folds in here).
- [ ] Functional coverage where it matters (e.g. the monbus packet-type
      matrix).
- [ ] Formal properties for the modules that warrant them
      ([[formal]]; the `formal/FORMAL_TODO.md` backlog folds in here).
- [ ] TB discipline holds: BFM usage, register access by name, seeds
      recorded ([[bfm-usage]], [[registers-by-name]], [[seeds-and-determinism]]).

### Gates and ordering

- Parts 2-3 subsume **DOCREV-009** (which itself absorbed DOCREV-008); when
  this task goes active, cut DOCREV-009's block here rather than running both.
- Inherits DOCREV-009's gates: do not start the docs parts until the
  DOCREV-001 area integrations are done and the README rollout (DOCREV-007)
  has settled the md set. Off-workstation critique rounds need DOCREV-005.
- Sequencing per the master Tasks INDEX: rtl/ areas before projects/.

### Done looks like

Per area: regressions green, formal green or gap-listed, docs measured
against the tree with a near-empty findings round, docs humanized, coverage
numbers on file with gaps triaged to tasks. The near-empty round is the
evidence — not the absence of looking.
