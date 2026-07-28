<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Closed (done)

_None._

---

## DOCREV-006 — Give math its own docs directory
**Status:** ✅ closed 2026-07-23 — moved, generator repointed, links verified

The RTL split had happened and the docs had not followed:

| | Before | After |
|---|---|---|
| RTL | `rtl/math/` (171) | unchanged |
| Tests | `val/math/` (119) | unchanged |
| Docs | `docs/markdown/rtl-common/math_*.md` (27) | **`docs/markdown/rtl-math/`** |

Math already built as its own PDF book (`RTL_Math_Library`) from its own index;
what it lacked was a directory matching where the RTL lives.

**Done:**
- 28 files moved with `git mv` (27 docs + `_book_math_index.md`) so history
  follows.
- New `rtl-math/index.md`, built from the "Arithmetic and Math Operations"
  section lifted out of `rtl-common/index.md`. Creating it also fixed all 27
  math docs' `](index.md)` sibling links for free — they resolve to the new
  index without edits.
- `rtl-common/index.md` now points at `../rtl-math/index.md` instead of carrying
  52 math links.
- `generate_rtl_pdfs.sh:99-101` repointed. It globs (`ls rtl-math/math_*.md`),
  so there is no file list to maintain.

**Deliberately NOT touched: `docs/review/kimi/`.** A first pass swept the Kimi
round files with the same rename and that was wrong — those are raw reviewer
evidence, and `FINDINGS.md` says in its own header "do not hand-edit the
tables; re-run it instead". Rewriting a critique to match a later
reorganisation destroys the record of what was actually reported. Reverted.

**So the math findings still cite `docs/markdown/rtl-common/math_*.md`.** That is
correct and should stay. The mapping is a 1:1 rename — `rtl-common/math_X.md` is
now `rtl-math/math_X.md` — so citations remain trivially resolvable. Regenerate
`FINDINGS.md` via `bin/review/index_findings.py` if its paths need refreshing;
do not sed it.


---

## DOCREV-012 — Validate the finding-adjudication pass (second model) on the next cdc qc round
**Status:** closed 2026-07-28 -- validated on reset-corpus cdc round_1, rule 10 written

## Outcome (2026-07-28)

**Round_1 (tightened brief): 3 findings, 0 false positives** -- against the
archived old-brief cdc series (13, 16, 12, 10, 5, 8, 7 findings in rounds
4-10, FP-heavy). All three were real and are fixed in the tree:

- `cdc.md` "Common mistakes" item 3 said pointers lag by `SYNC_STAGES`;
  the FIFOs' parameter is `N_FLOP_CROSS` (SYNC_STAGES belongs to the
  handshake/open-loop modules).
- `gaxi_fifo_async.md` test matrix said "1.25x ratio (10ns : 12ns)" --
  12/10 is 1.2x. The reviewer flagged the wrong rows (self-refuting nit);
  the VERIFIER found the real row while adjudicating it.
- `glitch_free_n_dff_arn.md` attribute snippet declared `r_q_array` twice
  (illegal if pasted); now one declaration with both attributes.

**Verifier vs human triage: 3/3 agreement AFTER tuning -- and the tuning was
the point.** The verifier REFUTED the SYNC_STAGES finding three times while
a human could see it was real. Each REFUTED was a distinct mechanical
evidence failure: first-finding's-quote-for-the-whole-file, un-normalized
quote matching, no identifier ground truth, and the finding's own reasoning
never reaching the prompt. All four fixed in `verify_findings.py`, plus a
format-compliance retry for the 2/3 UNPARSED rate on the first pass. Lessons
are handbook rule 10 ([[kimi-review-rounds]]).

Original task text below.


**2026-07-28 corpus reset:** the "next cdc qc round" is now the FRESH cdc
round (round_1 of the reset corpus) — the first area under DOCREV-013. The
previous cdc rounds whose FP rate is the comparison baseline live in
`~/rtl-doc-review/archive-pre-reset-2026-07-28/results/qc-kimi-k3/round_{4..10}/`
(13, 16, 12, 10, 5, 8, 7 findings respectively).

False positives are currently filtered by hand at triage -- the expensive
place. Two mitigations landed 2026-07-28:

- `bin/review/REVIEWER_BRIEF.md` gained a witness requirement (every finding
  must quote BOTH the doc text and the contradicting RTL + a concrete failing
  scenario) and a known-false-positive-classes section seeded from prior
  rounds (CRC-64/WE, packaging artifacts, free design choices, generated
  files).
- `bin/review/verify_findings.py` + `VERIFIER_BRIEF.md`: each finding is
  re-adjudicated by a SECOND model family (default claude-opus-5 via
  ANTHROPIC_API_KEY or the operator key file) under a refute-by-default
  brief. Verdicts land in `<round>/verdicts-<model>.md`; resume-safe, never
  overwrites. Findings resting on external constants are tagged
  NEEDS-RECOMPUTE (models quote sibling variants; arithmetic settles those).

**Validation:** run the next cdc qc round with the tightened brief, then
adjudicate its findings. Compare (a) FP rate vs previous cdc rounds, (b)
verifier UPHELD set vs the human triage of the same round. If the verifier's
REFUTED set contains a finding human triage confirms, the brief is too
aggressive -- tune before trusting it.

**On success:** write the lesson into [[kimi-review-rounds]] as rule 10
(witness requirement + second-model adjudication), per the house rule that
method lives in the handbook, not beside the tool.
