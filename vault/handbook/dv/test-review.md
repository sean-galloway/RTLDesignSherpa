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

   **Check the mechanism, not the string, and do it with a parser.**
   `REG_LEVEL` read only to decorate the test name passes a naive grep and
   selects nothing; that was the state of 8 val/common tests. Use the tool:

       python3 bin/review/check_test_levels.py val/<area>

   It walks the AST, so any function that reads REG_LEVEL and branches on a
   level literal counts as a grid whatever it is named, and it searches for
   TEST_LEVEL across the test file plus its resolved TBClasses imports.

   *Three regex versions of this check were written before the parser, and
   each produced a different set of false positives on the same area -- one
   required a generator named `generate_*params*` and missed
   `generate_test_parameters`; the next missed `get_cam_params`; a third used
   a fixed character window and missed grids whose REG_LEVEL read sits far
   from the level literal. The count moved 24 -> 16 -> 6 -> 4 and some
   "findings" were compliant tests every time. A scan that cries wolf gets
   ignored.*

   **That AST scan was itself wrong, and its green line was quoted for four
   days (2026-08-05).** It checked the depth half with `'TEST_LEVEL' in <test
   text + TB text>` -- a substring search, satisfied by the name appearing in a
   comment. It reported **common 48/48 compliant** while SIXTEEN tests had a
   depth mechanism that could not move: seven wrappers never put TEST_LEVEL in
   `extra_env` at all, eight pinned `test_levels = ['full']` in all three
   REG_LEVEL branches, and `test_dataint_crc` exported a varying value to a TB
   that never read it. The external test round found them one file at a time;
   the tool had certified every one.

   The lesson is the same one three regex versions taught, one level up:
   **presence is not wiring.** The rewrite moved from "is the string there" to
   "is the name read" and stopped, when the question is whether the value is
   EXPORTED by the wrapper, VARIES across levels, and is CONSUMED by the TB.
   The tool now checks all three on the AST and reports which one failed.

   Two calibration notes from fixing it, both false-positive sources:
   scanning the whole module for level literals passes every pinned test (they
   all mention some level somewhere), while reading only the assignment to
   `test_level(s)` fails a compliant lookup-table form
   (`test_level_map.get(reg_level, 'gate')` holds just the default). One level
   of indirection through referenced names is what distinguishes them.

   Per-area state, corrected: **common 32 of 48 (2026-08-05)**.
   cdc, math and amba have not been re-measured with the parser -- the older
   grep-based snapshot (2026-07-28) read cdc 6/13 and 10/13, common 42/48 and
   32/48, math 119/119, amba 55/117 and 68/117, and the common figures in it
   were wrong in both directions, so treat the rest as unmeasured until the
   tool is run on them.

   **The chain must follow Pattern B imports (fixed 2026-09-09).** `tb_chain`
   resolved only `TBClasses...` imports, so for a projects/components test
   whose TB lives in its own `dv/tbclasses` the depth read was invisible:
   a TB that read TEST_LEVEL and one that never did both printed
   `depth:never-read`. The bridge audit's 0 of 40 was right for the wrong
   reason and would have stayed 0 of 41 after the fix. It now follows
   `projects....` imports as well, one level plus their own. Re-measured
   with that: **bridge 41 of 41**, stream fub 2 of 7, apbx-xbar 0 of 6 --
   those two are real, and unmeasured before.

   **The grid is per file, not per area.** The house form (every val/common
   wrapper) is a generator in the test file that reads REG_LEVEL and
   branches on GATE/FUNC/FULL. A shared helper imported from a tbclasses
   module is DRY and invisible to the check, and the check is the
   enforcement; the bridge keeps its depth PROFILE shared in
   `bridge_levels.py` and its 8-line grid inline in each wrapper (generated
   files get it from the template).

   **A generated suite is only as current as the last regenerate, and the
   audit has to regenerate to know.** The bridge template had drifted from
   its 36 generated tests for months: the tree carried the real arbitration
   test that a43b032dd hand-edited into seven generated files (the template
   still emitted the TODO stub), two hand-written tests inside the generated
   2x2 file, and a TB method the template lacked -- and the template itself
   had a defect that made regeneration impossible, the BRIDGE-009 internal
   subtractive slave templated as a real slave with a BFM on pins that do
   not exist. Nobody regenerated because regenerating broke everything, and
   because it broke everything nobody found out why. Measure it by rendering
   into a scratch directory and diffing; note the bridge batch manifest
   carries its own output paths, so `--bulk` writes into the tree whatever
   `--output-*` says (that measurement overwrote 72 files once; `git
   checkout` recovered them). Hand-written tests for a generated DUT go in
   their own hand-written file beside the generated one
   (`test_bridge_2x2_rw_tracking.py`), never inside it.

2. **Structure -- TB separation is a HARD REQUIREMENT (Sean, 2026-08-03).**
   The TB class lives OUT of the test runner (bin/TBClasses/ for shared,
   project dv/tbclasses/ for project-specific); the runner is a thin
   include + parameter grid. Also: the three mandatory methods
   (setup_clocks_and_reset / assert_reset / deassert_reset); Pattern A vs B
   never mixed; pytest function name embeds the exact module name.
3. **Sources from the filelist**, never a hand-listed array.
4. **Seeds recorded** - SEED captured from env and logged
   ([[seeds-and-determinism]]).
5. **Framework usage** - protocol driving through framework BFMs/monitors,
   not hand-rolled protocol FSMs in the test ([[bfm-usage]]); register
   access by name where a regmap exists ([[registers-by-name]]).
6. **It actually checks.** Assertions/scoreboard on outputs; a
   stimulus-only test that always passes is a finding (the silent-pass
   mode, [[kimi-review-rounds]] rule 8's TB twin).

   **A checker's verdict needs a count behind it (2026-09-09).** The bridge's
   AXI5 sign-off test attached `AXI5ComplianceChecker` and asserted zero
   violations for a month while the checker had never bound: its monitors
   were built without a `protocol_type`, every sideband field was required,
   setup failed, the failure was logged at WARNING and swallowed, and the
   report said `compliance_checking: disabled` -- which reads as zero
   violations to anyone who only asks for the violation count. It surfaced
   the day the generated TBs armed the checker on every AXI5 port and the
   summary line printed empty statistics. When a test cites a checker,
   monitor, or scoreboard, look for the number it counted: an armed checker
   that performed zero checks and a disarmed one are the same finding.

   **It happened twice, two layers apart, within a day.** The second: the
   checkers resolved their port prefix by plain concatenation, so a port
   written `cpu_m_axi` rather than `cpu_rd_axi_` matched no channel signals
   at all -- no monitors, no loops, and a report still saying `enabled` with
   zero violations. It surfaced only because the consuming TB had by then
   been made to assert `checks_performed > 0`; the verdict itself looked
   perfect. Both are fixed, and `get_compliance_report()` now carries
   `armed` and `channels` so a caller can refuse a verdict with nothing
   behind it. Write the assertion on the count.
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
