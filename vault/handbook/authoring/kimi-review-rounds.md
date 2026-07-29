---
title: Kimi review rounds
summary: External doc review and humanization via Kimi - bundle, dispatch, rounds, the eight rules each failure taught, and the direct-mode runbook (model kimi-k3, key off-repo).
---

# Kimi review rounds

Documentation gets critiqued by an external reasoning model (Kimi/Moonshot)
before it is published. Two round types share one pipeline:

| Mode | Sent | Brief | Answers |
|---|---|---|---|
| `qc` | `DOCS.md` + `RTL.sv` | `bin/review/REVIEWER_BRIEF.md` | is this doc TRUE against the RTL? |
| `humanize` | `DOCS.md` only | [[humanization-voice]] | does it read like a person wrote it? |

The humanize pass deliberately withholds the RTL. Given ground truth, the
model re-litigates technical content instead of rewriting prose, and you get a
critique when you asked for a draft.

## Machinery

    bin/build_review_bundle.py     rebuild ALL units from the working tree
    bin/review/run_batch.py        dispatch a batch, serial, into a round
    bin/review/kimi_client.py      transport + the budget ladder

A unit is a directory holding `DOCS.md` (+ `RTL.sv` for qc). Books too large
for one call are pre-split into `parts/part_NN`. Results land in
`<results>/<mode>-<model>/round_N/` as `<unit>.md` + `<unit>.meta.json`,
with the inputs snapshotted into `_bundle_snapshot/`.

## The ten rules

Each one is here because ignoring it cost real work.

1. **Rebuild everything, send a subset.** Selection belongs at send time
   (`--only`/`--skip`), never in the bundler. A stale or partial bundle
   produces findings indistinguishable from real ones - the reviewer reports
   defects that were already fixed and you cannot tell which from the output.
   *Case: cost one full review pass.*
2. **Serial dispatch.** Concurrent sends interleave failures and make them
   hard to attribute to a unit.
3. **Never overwrite a round.** Round numbers auto-increment and an existing
   directory is refused. The critiques are the work product and are not
   reproducible without re-spending the tokens. *Case: a round was lost once.*
   Resuming an interrupted round fills gaps only - it never rewrites a unit
   that already succeeded.
4. **Explicit large `max_tokens`.** Kimi is a reasoning model and reasoning is
   drawn from the completion budget, so an under-budgeted call returns *empty
   content* with `finish_reason=length` - not an error, just nothing. Ladder:
   32768 -> 65536 -> 131072. If a unit still truncates at 131072, **split it in
   the bundler**; do not raise the ceiling. *Case: cdc_part_01, math_part_02
   and shared_part_02 all needed 131072 in round_2.*

   The budget runs out in **two** ways and only one of them is loud. Empty +
   `finish=length` is obvious. *Partial* + `finish=length` - a critique cut off
   mid-sentence - is filed as a successful unit, so findings that were never
   emitted read as findings that do not exist, and the unit's low finding count
   looks like a clean area. **Escalate on `finish_reason == "length"` whatever
   came back**, never on emptiness alone. *Case: `common_part_04` in the
   2026-07-24 common round returned 2,586 chars (against 10k-12k for its
   siblings), cut off mid-expression inside its second finding, with
   `budget_escalations: 0` - the ladder never fired because the body was
   non-empty. Two visible findings; unknown how many lost.* Check every round
   for `finish_reason: length` in the `.meta.json` before triaging, and treat a
   unit whose output is a fraction of its siblings' as suspect.
5. **Verify every finding against the RTL before acting.** Reviewers report
   wrong things confidently when a unit was mis-packaged. *Case: the
   `math_subtractor` "five nonexistent modules" finding was our packaging bug,
   not the reviewer's error.*

   Reviewers are also wrong about the *outside world*, not just this repo, and
   those errors are the most persuasive because they arrive with a citation.
   *Case: k3 round_2 called `dataint_crc.md`'s CRC-64/ECMA-182 config wrong and
   cited check value `0x62EC59E3F1A4F00A` for init/xorout = FF. Computing the
   documented config gives `0x6C40DF5F0B497347`, which IS the published
   ECMA-182 check value; the reviewer had quoted CRC-64/WE. The doc was right.*
   When a finding rests on an external standard, **recompute it** - a twenty-line
   reference implementation settles it, and validating that implementation
   against a second published vector (CRC-64/XZ here) proves the tool before you
   trust its verdict.

   The converse also holds: a finding that *looks* like a doc nit can be a real
   RTL defect. Read the whole finding, not the headline. *Case: "RTL rotates
   the wrong direction" in `arbiter_round_robin_simple` reads like a doc-vs-RTL
   ordering mismatch - and grant order genuinely is a free choice - but the
   same finding also claimed starvation, which was true: two of four agents
   were never served. Triage doc-fix vs RTL-fix per finding before batching.*
6. **Fix EVERY occurrence, not the one the finding quotes.** A reviewer cites one
   instance; the same wrong claim is usually repeated in the same file, on a
   sibling page, and in the RTL header comment. Grep the claim, not the quote.
   *Case: round_4 flagged "any even depth" for Johnson and `johnson2bin` being
   "registered". Both were fixed at the quoted line. Round_5 found the DEPTH row
   of the SAME parameter table still saying "any even value", the dependencies
   list still saying "(registered)", and three more "(registered)" in
   `rtl/cdc/*.sv` header comments.* Earlier the same round showed the reset and
   depth claims had been fixed on `apb5_slave_cdc.md` and never propagated to its
   APB4 sibling, leaving two pages contradicting each other about one FIFO.

   **Sweep for the CLAIM, not for the wording.** The same "any even depth" error
   survived into round_6 and again into round_7 -- four rounds -- because each
   sweep matched the strings previously seen (`any even number|value|depth`)
   while the surviving instance said "any even **count**". A sweep built from
   the last finding's vocabulary finds the last finding. Search the loose
   concept (`even`, then read every hit), and follow it into the RTL: the
   round_7 instance traced back to a comment in `gaxi_fifo_async.sv`, which is
   where the doc claim had been copied from in the first place. **Fix the source
   comment or the doc error regrows.**

   **Verify a fix by reading the result, never by re-running the pattern the fix
   used.** A `re.sub` that matches nothing raises nothing, so a fix can silently
   no-op; if the verification grep carries the same assumption, it agrees. *Case:
   round_4's "dependency direction backwards" fix used a regex with a space where
   the file had a newline. It matched nothing, the verification grep used the
   same pattern and also matched nothing, and I reported FIXED. Round_5 found the
   identical sentence untouched.* Read the file back, or assert on the NEW text
   being present -- an assertion that fails when the edit did not apply.

   The corollary: **a partial fix costs a whole extra round.** Round_5 found MORE
   on its unit than round_4 did (11 vs 8), and three of those eleven were my own
   incomplete work -- including a contradiction I created by correcting a latency
   table and leaving the Overview promising the opposite.

7. **Integration status is MEASURED, never inferred from commit history.**
   Before claiming a round is integrated, check the findings against the tree.
   Cheap first pass: for every file a round implicates, has it been committed
   since the round date? Then spot-check two or three findings against the RTL
   directly, because a touched file is not a fixed finding.

   *Case: a `docs(amba/monitor): reconcile all monitor documentation with the
   RTL` commit reads exactly like an integration pass. round_3 was sent SIX
   HOURS LATER, reviewed the post-reconcile docs, and still returned 70
   confirmed defects. Measured: round_2 had 1 of 102 implicated files touched
   since review, round_3 had 0 of 31 - nothing was integrated.* A
   reconcile-shaped commit message is not evidence.
8. **Verify a fix with a clean rebuild, and mutation-check the test.** "It
   passes now" is worth nothing on its own; two silent-pass modes make a green
   run look like proof when it is not.

   - **Stale build.** Verilator reuses an existing `sim_build`, so a test can
     "pass" against a binary built from the OLD RTL. *Case: a pumice test
     passed in 0.41 s - impossible for a build plus sim. Clean rebuild took
     6.07 s and genuinely passed, but a reverted-RTL experiment run on that
     stale binary would have proved the exact opposite of the truth.* Always
     `rm -rf` the build dir before a before/after comparison ([[running-regressions]]).
   - **Stimulus that cannot expose the bug.** *Case: the first regression test
     written for the arbiter starvation fix passed against the BROKEN RTL,
     because no profile saturated all requesters, so the arbiter was never
     cornered.* Revert the fix, confirm the test goes RED, restore. An
     assertion that never fails on the bug it was written for is decoration.
     See [[randomization]] and [[formal]].
9. **Sweep the area's meta-docs, not just its module pages.** A Kimi bundle is
   module docs plus RTL, so it never sees the area's `README.md` / `PRD.md` /
   `overview.md` - and those rot hardest, because a structural change updates
   the RTL and leaves the summary behind. When reviewing an area, audit them by
   hand against [[doc-placement]]:

   - **Count and category drift.** *Case: `rtl/common/README.md` claimed "86
     modules across 9 categories" after the arithmetic split left 55; the
     matching `docs/markdown/rtl-common/overview.md` still listed "Arithmetic &
     Math (25+ modules)" as a live category. Both copies rotted because the
     split doubled the update burden - the exact failure the one-source rule
     predicts.* Recompute counts from `ls rtl/<area>/*.sv`.
   - **Methodology in the RTL tree.** A style guide, a how-to, or a standalone
     guide beside the code is misplaced - it belongs in `vault/handbook/` (method)
     or `docs/markdown/` (a reader-facing guide). *Case: a 17 KB
     `DOCUMENTATION_STYLE_GUIDE.md` sat in `rtl/common/`; moved to
     [[module-doc-template]].*
   - **A README beside code should be a link, not a second copy.** *Case:
     `rtl/common/README.md` was a 14 KB standalone quick-start; the guide moved
     to `docs/markdown/rtl-common/quickstart.md` and the RTL file became a
     pointer.*

   The authority on where each kind of doc lives is [[doc-placement]].

10. **Filter false positives with a second model, then TUNE IT against human
    triage before trusting it.** Hand triage is the expensive place to catch
    FPs. The pipeline: the reviewer brief carries a witness requirement (every
    finding quotes BOTH the doc text and the contradicting RTL plus a concrete
    failing scenario) and a known-FP-classes section; `verify_findings.py`
    then re-adjudicates each finding with a DIFFERENT model family under a
    refute-by-default brief (`VERIFIER_BRIEF.md`), resume-safe, with
    NEEDS-RECOMPUTE tags on findings resting on external constants (rule 5).

    The first live run (reset-corpus cdc round_1, 2026-07-28) upheld 3 of 3
    after tuning - but it REFUTED a finding human triage had confirmed THREE
    times running, and each failure taught a separate mechanical fix, all now
    in the tool:

    - **Adjudicate the finding, not the file.** The evidence locator took the
      first `Says:` quote in the critique FILE, so the second finding in a
      unit was adjudicated against the first finding's evidence. Each finding
      gets its own block, and the block's full text (Says/Actually/Impact)
      goes in the prompt - adjudicating a bare title invites the verifier to
      under-weight the reviewer's actual argument.
    - **Normalize before quote location.** Critiques re-wrap and de-backtick
      the lines they quote; a raw substring search misses and the evidence
      silently degrades to the head of the file. Strip emphasis, collapse
      whitespace, match on both sides.
    - **Hand the verifier the grep.** Wrong-identifier findings are settled by
      WHERE each identifier appears, and a model reading a 200k-char
      concatenated RTL.sv does not cross-check reliably - it anchored on
      `SYNC_STAGES` existing in the handshake modules and REFUTED, when the
      finding was that the FIFO section used that name for `N_FLOP_CROSS`.
      `verify_findings.py` now appends an identifier ground-truth table
      (grep of every backticked/UPPER_SNAKE token in the finding across the
      snapshot).
    - **Format-compliance retry.** Two of three first-run verdicts came back
      as prose rambles with no `VERDICT:` line (one even concluded "finding
      is self-refuting" without saying REFUTED). One follow-up turn -
      "reply with EXACTLY this format" - recovers it; record UNPARSED only
      after that retry fails.

    The validation rule stands: if the verifier's REFUTED set contains a
    finding human triage confirms, the brief or the evidence pack is too
    weak - tune before trusting. DOCREV-012.

## Endpoint

The key is never in a script. Locally the chain is
scripts -> litellm proxy on `localhost:4000` (dummy token `sk-x`) -> Moonshot,
with the real key behind the proxy. Anywhere else there is no proxy, so the
scripts read the endpoint from the environment instead:

| | `KIMI_BASE_URL` | `KIMI_API_KEY` | `KIMI_MODEL` |
|---|---|---|---|
| local | `http://localhost:4000/v1` (default) | `sk-x` (default) | `kimi-k2` (default) |
| direct | `https://api.moonshot.ai/v1` | real Moonshot key (see runbook) | **`kimi-k3`** (required) |

`kimi-k2` is a **proxy alias** routed to the frontier model, not a model name;
sending it to `api.moonshot.ai` returns 404. `run_batch.py` preflights this and
refuses to start, because the alternative is discovering it deep into a serial
round. See [[cloud-sandbox]] for running a batch off the workstation.

Proxy launch, if it is down:

    source /mnt/data/github/seans-cli-ai-local/config/frontier-keys.env
    ~/vllm-env/bin/litellm --config \
        /mnt/data/github/seans-cli-ai-local/config/litellm-config.yaml
    # health check:
    curl -s http://localhost:4000/v1/models -H "Authorization: Bearer sk-x"

The key chain is: `MOONSHOT_API_KEY` in `frontier-keys.env` (untracked, one
disk) -> sourced into the proxy's environment -> referenced by
`litellm-config.yaml` as `os.environ/MOONSHOT_API_KEY`. The key is never in a
script and must never be committed.

Do not `pkill -f litellm` to restart the proxy - target the PID. A broad pkill
once killed the working shell.

## Running it -- the direct-mode runbook

The proxy above is for the workstation that had litellm on `localhost:4000`. On
any other box there is no proxy: run **direct** against Moonshot. This is the
step-by-step that works, so it does not get re-derived each time.

**Model: always `kimi-k3`.** Not `kimi-k2` (that is a proxy alias and 404s
against `api.moonshot.ai`), not `kimi-k2.6/.7`. `KIMI_MODEL=kimi-k3`, always.

**Key: loaded inline, NEVER written into the repo -- not even its location.**
The Moonshot key lives in the operator's private out-of-repo secrets store (ask
Sean where; it is deliberately not recorded here). Load it into `KEY` at command
time from wherever that is; do not echo it, and do not put it -- or the path to
it -- in `env_python`, a `.env`, a script, or any tracked file.

    KEY=<load the Moonshot key from your out-of-repo secrets store>
    # sanity: `curl -s -o /dev/null -w '%{http_code}' https://api.moonshot.ai/v1/models
    #          -H "Authorization: Bearer $KEY"` should print 200

**Everything off-repo.** The bundle and the raw results live OUTSIDE the working
tree (`~/rtl-doc-review/{books,results}`) -- confirm with
`git ls-files --error-unmatch` before pointing anything there. Since the
2026-07-28 reset the raw run is not vendored into the repo at all (the old
`docs/review/kimi/` practice ended with the reset); curated summaries live in
the vault task pages instead.

The three commands, serial, correctness before voice:

    # 1. rebuild the WHOLE bundle from the current tree (rule 1: send a subset, build all)
    python3 bin/build_review_bundle.py ~/rtl-doc-review   # writes ~/rtl-doc-review/books/

    # 2. correctness pass for one area (dry-run first to see the units)
    KEY=<load the Moonshot key from your out-of-repo secrets store>
    KIMI_API_KEY=$KEY KIMI_BASE_URL=https://api.moonshot.ai/v1 KIMI_MODEL=kimi-k3         python3 bin/review/run_batch.py qc         --books ~/rtl-doc-review/books --results ~/rtl-doc-review/results         --only common --dry-run
    # drop --dry-run to send. Serial; a 20-unit round takes well over an hour.
    # --resume N re-enters round_N and sends only its missing units.

**`--books` takes `<OUT>/books`, not `<OUT>`.** The bundler is given the parent
and creates `books/` underneath it; pointing `--books` at the parent matches no
units and the run exits with a bare `no units matched` -- which reads like an
empty bundle, not a wrong path. *Case: a `--books ~/rtl-doc-review/bundle`
invocation logged exactly that and was mistaken for a bundler failure; it also
left a second stale bundle tree at `<OUT>/bundle/books` that a later round was
nearly sent from.* Keep ONE bundle root and always dry-run first -- the dry run
prints the unit list, so a path mistake is visible before any tokens are spent.

    # 3. humanize -- ONLY after correctness is integrated (never voice-pass a wrong doc)
    KIMI_API_KEY=$KEY KIMI_BASE_URL=https://api.moonshot.ai/v1 KIMI_MODEL=kimi-k3         python3 bin/review/run_batch.py humanize         --books ~/rtl-doc-review/books --results ~/rtl-doc-review/results --only common

**Coverage gap -- the meta-docs.** `build_review_bundle.py` builds a unit per
`docs/markdown/**/_book_*_index.md` and includes only the docs that index
*links* -- which is `overview.md` + the module pages, NOT `index.md`,
`quickstart.md`, or a section `README`. For a "send ALL md" pass (DOCREV-009),
add the missing meta-docs as their own unit under `<OUT>/books/<area>_meta/`
(a `DOCS.md` of the meta-doc text + an `RTL.sv` listing the area's module names
as ground truth for count/existence claims). `--only <area>` then covers both
`<area>` and `<area>_meta` by prefix.

A `_meta` unit is HAND-BUILT, and **`build_review_bundle.py` DELETES it** --
the rebuild clears `<OUT>/books/` wholesale, so the unit is simply gone
afterwards. (An earlier version of this note claimed the bundler left `_meta`
alone and let it go stale. Observed behaviour as of 2026-07-27 is deletion; if a
round reports "no units matched" for `<area>_meta`, this is why.) Either way the
rule is the same and it is not optional: **regenerate every `_meta` unit
immediately after every bundle rebuild, from the tree, never by editing the
previous copy.**

Golden deps scale-guard (2026-07-29): `augment_golden_deps.py` SKIPS a book
whose doc references exceed 25 distinct modules. Catalog-style books (math:
120+ backticked module mentions in tables) would otherwise get the whole
library appended to every part, undoing the size split -- the `_meta`
inventory unit is the existence/count ground truth for those, not source
dumps. Golden is for reset_sync-class external primitives, small counts only.

Build it from a script, not by hand -- a hand-maintained inventory is exactly
what goes stale:

```python
import os, glob
B = os.path.expanduser('~/rtl-doc-review/books/<area>_meta'); os.makedirs(B, exist_ok=True)
mods = sorted(os.path.basename(p) for p in glob.glob('rtl/<area>/*.sv'))
rtl  = ["// <area> meta-docs -- ground truth is the module inventory, not full source.",
        f"// Verify count/category/existence claims against rtl/<area>/*.sv ({len(mods)} modules):", ""]
rtl += [f"//   {m}" for m in mods]
open(f'{B}/RTL.sv', 'w').write("\n".join(rtl) + "\n")

pages = ['docs/markdown/<book>/index.md', 'docs/markdown/<book>/overview.md']
doc = ["# <book> meta-docs (index + overview)", ""]
for p in pages:
    doc += [f"<!-- SOURCE FILE: {p} -->", "", open(p, encoding='utf-8').read(), ""]
open(f'{B}/DOCS.md', 'w').write("\n".join(doc))
```

*Case: after the CDC modules moved out of `rtl/common`, a surviving
`common_meta/RTL.sv` listed 56 modules against an actual 49 -- ground truth that
was itself wrong, which would have produced count findings the reviewer could
not get right either way.* When an area's modules have moved, say so in the
`RTL.sv` header (list the new location's inventory too) so "doc claims X lives
here" is separable from "X does not exist".

## The order: correctness until clean, then voice

**An area runs `qc` rounds until a round comes back clean or with nothing but
false positives. Only then does it get `humanize`** (Sean, 2026-07-27).

One qc round is not a clean bill of health. A round finds what it finds; fixing
those findings changes the pages, and the changed pages have not been reviewed.
Re-running until a round produces nothing actionable is what makes "correct"
mean something -- and false positives are an acceptable stopping point, because
a reviewer that only misreads has run out of real defects to find.

The reason this matters more for `humanize` than for any other step: a voice
pass REWRITES every page. Voice-passing a page that is still wrong produces a
well-written falsehood, and the rewrite makes the error harder to spot later
because it no longer reads like something copied from stale RTL.

Two failure shapes this ordering prevents, both seen on this repo:

- **A single qc round mistaken for done.** `common` had qc round_2 integrated,
  and the humanize pass that followed was correct to run. `cdc` had only the old
  proxy-corpus round, taken before the CDC reorg, so its `index.md`,
  `overview.md` and consolidated `cdc.md` had never been checked in their
  current form when the voice pass ran. That ordering was wrong, and a second qc
  round is what fixes it.
- **Documenting a state that has since changed.** The `rtl-integ-amba` pages
  were written while the RTL was broken, the RTL was fixed four hours later, and
  the pages still said "does not build" until a qc round caught it. Docs written
  against a moving target need a qc round AFTER the target stops moving.

**Wait for the whole round before acting on it.** Nothing gets fixed while
multitasking -- one area's correctness round runs to completion, gets integrated
and verified, and only then does the next area or the humanize pass start.

**The humanize bundle is rebuilt AFTER the last correctness integration, not
carried over from the qc round.** Rule 1 applies to voice passes too, and it
bites in a specific direction here: the humanizer rewrites every page, so a
bundle built before the last integration makes the applier CLOBBER that
integration's fixes with pre-fix prose. *Case: the 2026-07-28 cdc humanize ran
from the round_4 qc bundle -- built before round_4's five fixes were applied --
and reverted every one of them on apply. The re-application was only cheap
because the fixes were small and listed. Rebuild the bundle between the last
correctness fix and the humanize send, every time.*

## State

**2026-07-28: the corpus was RESET (Sean).** All prior rounds are archived to
`~/rtl-doc-review/archive-pre-reset-2026-07-28/` and removed from the tree;
the vendored proxy corpus (`docs/review/kimi/`) survives only in git history.
The trigger: seven cdc rounds in two days (k3 rounds 4-10: 13, 16, 12, 10, 5,
8, 7 findings) without converging - the area was being re-litigated, not
closed, and every round was paying full re-review cost on an area whose fixes
were being integrated between rounds. Backlog integration (DOCREV-001) is
dropped with it; fresh per-area rounds under the tightened REVIEWER_BRIEF
(witness requirement) and second-model adjudication (`verify_findings.py`)
replace it, in the order cdc, common, math, amba, projects/components
(DOCREV-013). Round numbering restarts at round_1 in the fresh results dir;
the pre-reset rounds cited in the rules above are the archived corpus.

The historical FP-rate baseline for the adjudication validation (DOCREV-012)
is the archived cdc series above. Pre-reset integration status tables live in
the git history of this note.

`bin/review/index_findings.py` flattens a round's critiques into per-round
counts, the most-implicated files, and a checkbox per finding.

Two critique layouts exist (`[CONFIRMED] title` with indented fields, and
`### F1` headings with bulleted fields). The indexer parses both; a parser that
handles only one silently undercounts the backlog, which reads as progress.

Related: [[doc-pipeline]] for how the reviewed Markdown becomes a deliverable.
