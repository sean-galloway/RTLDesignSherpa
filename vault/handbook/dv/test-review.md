---
title: Test review rounds
summary: Auditing test collateral with the review pipeline - what to grab from the repo, bin/TBClasses, and the RTLDesignSherpa-DV framework; the bundle layout; the audit checklist.
---

# Test review rounds

The test-audit half of the per-area work (DOCREV-013 phase (b), AUDIT-001
part 4). Same pipeline shape as the doc review ([[kimi-review-rounds]]):
bundle -> qc round -> `verify_findings.py` adjudication -> human triage ->
integrate -> stop by the impact rule. What differs is WHAT gets bundled and
WHAT the reviewer checks.

## The three sources of truth

All validation collateral descends from one cocotb-based source per layer:

| Layer | Where | Role in the bundle |
|---|---|---|
| Test files | `val/<area>/test_*.py` (this repo) | the audit TARGET |
| Shared TB classes | `bin/TBClasses/**` (this repo) | audit target (they hold the scenario generators the tests include) |
| Framework | `$RDS_DV_REPO` (default `/home/seang/github/RTLDesignSherpa-DV`), `src/CocoTBFramework/**` | GOLDEN evidence - reviewed in its own repo, never a finding target. The local clone is a **recent download for convenience only** (Sean, 2026-07-28): read it, never edit it, and read no meaning into its git state - it is not the working copy. |
| RTL under test | the test's filelist (`rtl/<area>/filelists/*.f`) | ground truth for port/param claims |
| The contract | `make/tests.mk`, handbook [[test-runner]], [[tb-structure]] | what "correct" means; the reviewer checks against it |

A `val/<area>/test_*.py` is almost exclusively: an include of a TB class
(inline or from `bin/TBClasses/`) that holds the actual tests and scenario
generators, plus a parameter generator (REG_LEVEL grid) handed to
`cocotb_test.run()`. The audit reads exactly that composition.

## The grab algorithm (per test file)

1. Parse `from TBClasses...` / `import TBClasses...`, resolve to
   `bin/TBClasses/` files, and recurse into their own TBClasses imports.
2. Parse `from CocoTBFramework...` in the test AND in every collected
   TBClasses file, resolve under `$RDS_DV_REPO/src/CocoTBFramework/`,
   recurse within the DV repo. (The venv's installed copy can drift from the
   repo; always read the REPO, which is git-controlled.)
3. Extract the test's `filelist_path=` - the RTL it builds comes from the
   filelist, never a hand-listed array ([[filelists]]; the counter_bingray
   silent-break lesson).
4. Record the REG_LEVEL grid and TEST_LEVEL gating for the checklist.

## Bundle layout (per area)

    test-review/<area>/
      MANIFEST.md       # test -> TB chain -> framework chain -> filelist, one line each
      TESTS.py          # the test_*.py, each behind a ===== path banner
      TB.py             # the collected bin/TBClasses files, path banners
      FRAMEWORK.py      # the CocoTBFramework chain, path banners; GOLDEN
      RTL_IFACES.sv     # module headers (parameter/port blocks) of the RTL under test

`FRAMEWORK.py` carries the same GOLDEN banner convention as the doc
bundles: present so claims about framework usage can be checked, never a
finding target. Full RTL bodies are deliberately excluded - the audit is
about test structure, and the doc-review bundle already covers the RTL; the
interface headers are enough for "does the test drive real ports".

## The audit checklist (per test)

1. **Three levels, both mechanisms -- HARD REQUIREMENT** ([[test-runner]]).
   REG_LEVEL grid in the pytest wrapper (GATE/FUNC/FULL produce different
   parameter counts) AND TEST_LEVEL depth gating inside the TB (gate < func <
   full actual work). Either missing = finding.

   **Grep for the mechanism, not the string.** `REG_LEVEL` read only to
   decorate the test name passes a naive scan and selects nothing; that was
   the state of 8 val/common tests. The check is whether the parameter
   generator BRANCHES on it:

       # a generator that branches, vs one that merely mentions REG_LEVEL
       def has_grid(src):
           gen = re.search(r'def generate\w*params\w*\(.*?\)(.*?)(?=\n@|\ndef |\Z)',
                           src, re.S | re.I)
           body = gen.group(1) if gen else ''
           return 'REG_LEVEL' in body and ('GATE' in body or 'FULL' in body)

   and whether TEST_LEVEL appears anywhere in the TB chain (test file plus its
   resolved TBClasses imports), not just in the wrapper. Snapshot 2026-07-28, REG_LEVEL/TEST_LEVEL presence: cdc 6/13,
   10/13; common 42/48, 32/48; math 119/119, 119/119; amba 55/117, 68/117.
2. **Structure.** TB class in the right place ([[tb-structure]]); the three
   mandatory methods (setup_clocks_and_reset / assert_reset /
   deassert_reset); Pattern A vs B never mixed; pytest function name embeds
   the exact module name.
3. **Sources from the filelist**, never a hand-listed array.
4. **Seeds recorded** - SEED captured from env and logged
   ([[seeds-and-determinism]]).
5. **Framework usage** - protocol driving through framework BFMs/monitors,
   not hand-rolled protocol FSMs in the test ([[bfm-usage]]); register
   access by name where a regmap exists ([[registers-by-name]]).
6. **It actually checks.** Assertions/scoreboard on outputs; a
   stimulus-only test that always passes is a finding (the silent-pass
   mode, [[kimi-review-rounds]] rule 8's TB twin).
7. **Levels are honest.** gate is genuinely fast; full is genuinely deeper,
   not gate re-labelled.

## Review flow

`bin/review/build_test_review_bundle.py` (to be written to this spec) builds
the bundle off-repo; `run_batch.py qc` sends it with a test-audit brief
variant; `verify_findings.py` adjudicates; human triage; integrate in the
owning area; stop by the impact rule. One area at a time, same as docs.

Related: [[test-runner]], [[tb-structure]], [[bfm-usage]],
[[seeds-and-determinism]], [[kimi-review-rounds]], [[coverage]].

## Adjudication lessons from round_1 (2026-07-29)

- **The verifier never saw the tests.** `verify_findings.py`'s evidence glob
  was `*.md`/`*.sv` only; testqc units are `.py`. 39/51 first-pass UNCERTAIN.
  Fixed, plus quote-bearing-first ordering (a huge golden FRAMEWORK.py head
  must not starve the cited file), plus a mechanical TEST SKELETON
  (generate_params / parametrize / run() / reset-method signatures) in every
  testqc verdict -- the deciding code sits far from the header docstring a
  finding's Says: quote usually cites.
- **Concatenated blobs conflate files.** TESTS.py is many test files behind
  `# FILE:` banners; a grep hit's line number does not say WHICH file it is
  in. The verifier REFUTED a true finding (test_cdc_2_phase_handshake has no
  REG_LEVEL) because the hit belonged to bin2gray. Identifier ground truth
  must report the source file (nearest preceding banner), not the blob line.
- **The contract must be IN the evidence.** Findings cite "Clause N" of
  TEST_REVIEWER_BRIEF.md, which was not in the pack; two verdicts REFUTED
  what they should have called UNCERTAIN (rule 4). Include the brief's
  contract clauses in the verifier's evidence for testqc rounds.
- Verdict quality after fixes: 14 UPHELD, 8 REFUTED (1 wrong, above), 29
  UNCERTAIN routed to human triage -- the verifier settles mechanical
  classes (SEED, level presence) and punts semantics, which is the right
  division.
