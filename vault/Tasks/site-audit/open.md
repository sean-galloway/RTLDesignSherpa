<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# site-audit — open

## AUDIT-002 — triage 11 tasks whose body status contradicts their page
**Status:** open 2026-08-28 — surfaced by `bin/check_task_ids.py`
**Priority:** P3 — bookkeeping, but it makes the rollup counts lie
**Area:** cross-cutting (common + pumice + amba) — filed here rather
than in `common/` because it is not common-area work; most of the
affected tasks happen to be COMMON-* but two are pumice and one amba.

`bin/check_task_ids.py` reports these as WARNINGS (it deliberately does not
auto-fix them):

    common:  COMMON-010, -014, -015, -016, -017, -018, -019, -021
    pumice:  PUMICE-010, PUMICE-011
    amba:    NEXYSA7-STREAM  (in closed.md, body says dropped)

Each lives in a terminal page (`closed.md` / `dropped.md`) while its body
still says `**Status:** open`. TWO different bugs are mixed in here and they
need OPPOSITE fixes, which is why it was not automated:

* **closed with a stale line** — the work is genuinely done and only the
  status text was never updated. Fix: update the line. (Session notes say
  COMMON-021 is this case: the covers were verified.)
* **still open and misfiled** — the work is NOT done and the task reached
  closed.md by mistake. Fix: move it back to `open.md`. (COMMON-010, "every
  module MUST have a filelist and a registry entry", reads like this one —
  and TASK-026 in amba is its shared gate, still open.)

Auto-flipping the text would launder the second kind into the closed pile,
which is worse than the inconsistency it fixes. Read each, decide, then the
warning count should reach zero.

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
      ([[coverage]]; that backlog now lives in `vault/Tasks/coverage/` —
      COV-001 is the remaining rollout).
- [ ] Functional coverage where it matters (e.g. the monbus packet-type
      matrix).
- [ ] Formal properties for the modules that warrant them
      ([[formal]]; the `formal/FORMAL_TODO.md` backlog folds in here).
- [ ] TB discipline holds: BFM usage, register access by name, seeds
      recorded ([[bfm-usage]], [[registers-by-name]], [[seeds-and-determinism]]).

### Gates and ordering

- Parts 2-3 subsume **DOCREV-009** (which itself absorbed DOCREV-008); when
  this task goes active, cut DOCREV-009's block here rather than running both.
- Inherits DOCREV-009's gates, UPDATED 2026-07-28 for the corpus reset:
  DOCREV-001 is dropped; the docs parts proceed area by area via DOCREV-013's
  fresh rounds (order: cdc, common, math, amba, projects/components, then
  assess fpga), each area starting with the four-line-Makefile check
  (`rtl/make/area.mk` + `make/tests.mk` leaves). The README rollout
  (DOCREV-007) settling the md set still gates humanization.
  Off-workstation critique rounds need DOCREV-005.
- Sequencing per the master Tasks INDEX: rtl/ areas before projects/.

### Done looks like

Per area: regressions green, formal green or gap-listed, docs measured
against the tree with a near-empty findings round, docs humanized, coverage
numbers on file with gaps triaged to tasks. The near-empty round is the
evidence — not the absence of looking.

### Evidence on file

**common — Part 1 regressions, 2026-08-05.** `make clean-all` first, then all
three levels via the area Makefile (never bare pytest):

| level | collected | result |
|---|---|---|
| gate | 75 | 75 passed |
| func | 208 | 208 passed |
| full | 925 | 925 passed |

No skips, no deselects, no xfails, and the pass count equals the collected
count at every level — so nothing is quietly not running. Checked per FILE as
well as in total: all 48 `test_*.py` collect at least one test at each of the
three levels. (Beware the obvious way to count that: a `test_[a-z_]*\.py`
pattern over pytest's node IDs also matches `con`**`test_base.py`** in the log
lines and reports 49.)

The full level was worth running on its own account — it caught
`test_counter_load_clear_wavedrom[8]`, dead since the grids were added:
`loadval` is `[$clog2(MAX)-1:0]`, so `MAX=8` is a 3-bit port while
`scenario_clear_operation` loads a match value of 8. It raised
`OverflowError: Int value (8) out of range for assignment of 3-bit signal`, and
only at FULL, where nothing else in the area runs that width. `MAX=8` is
meaningless for that diagram anyway — a counter that wraps at 8 can never match
8. Grid is now `[16, 32, 64]` and the TB refuses `MAX < 16` with a message that
names the grid entry instead of the assignment.

Still outstanding for common: Part 4 coverage (never measured), the formal gaps
(53/58 pass, 4 prove-only, 1 error — `counter_freq_invariant`, yosys parse),
and a test-audit round_2 (round_1's fixes rewrote much of what it reviewed).
