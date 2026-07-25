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

## The eight rules

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
6. **Integration status is MEASURED, never inferred from commit history.**
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
7. **Verify a fix with a clean rebuild, and mutation-check the test.** "It
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
8. **Sweep the area's meta-docs, not just its module pages.** A Kimi bundle is
   module docs plus RTL, so it never sees the area's `README.md` / `PRD.md` /
   `overview.md` - and those rot hardest, because a structural change updates
   the RTL and leaves the summary behind. When reviewing an area, audit them by
   hand against [[doc-placement]]:

   - **Count and category drift.** *Case: `rtl/common/README.md` claimed "86
     modules across 9 categories" after the arithmetic split left 55; the
     matching `docs/markdown/RTLCommon/overview.md` still listed "Arithmetic &
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
     to `docs/markdown/RTLCommon/quickstart.md` and the RTL file became a
     pointer.*

   The authority on where each kind of doc lives is [[doc-placement]].

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
tree (e.g. `~/rtl-doc-review/{bundle,results}`) -- confirm with
`git ls-files --error-unmatch` before pointing anything there. The raw run is
not committed; only the curated critiques land in `docs/review/kimi/round_N/`.

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

A `_meta` unit is HAND-BUILT and the bundler neither regenerates nor deletes it,
so it survives a rebuild while silently going stale -- the one failure mode the
rebuild-everything rule exists to prevent. **Regenerate every `_meta` unit by
hand whenever the bundle is rebuilt.** *Case: after the CDC modules moved out of
`rtl/common`, the surviving `common_meta/RTL.sv` still listed 56 modules against
an actual 49 -- ground truth that was itself wrong, which would have produced
count findings the reviewer could not get right either way.* When an area's
modules have moved, say so in the `RTL.sv` header (list the new location's
inventory too) so "doc claims X lives here" is separable from "X does not exist".

**Wait for the whole round before acting on it.** Nothing gets fixed while
multitasking -- one area's correctness round runs to completion, gets integrated
and verified, and only then does the next area or the humanize pass start.

## State

Critiques are vendored into `docs/review/kimi/round_N/` (532 KB). The
`_bundle_snapshot/` inputs (11 MB) stay out - they are regenerable from git at
the reviewed commit. `bin/review/index_findings.py` flattens every critique
into `docs/review/kimi/FINDINGS.md`: per-round counts, the most-implicated
files, and a checkbox per finding.

**Round numbers are per-results-directory, and there are now TWO.** The original
proxy corpus (`kimi-k2` via litellm) is vendored in `docs/review/kimi/round_N/`.
The direct-mode `kimi-k3` runs start their own numbering under
`<results>/qc-kimi-k3/round_N/`. So "round_2" is ambiguous unless you say which
- they are different corpora over different areas at different commits. Always
qualify: *proxy round_2* vs *k3 round_2*.

Proxy corpus (`docs/review/kimi/`):

| Round | Units | Findings | CONFIRMED | Integrated? |
|---|---|---|---|---|
| round_1 | 8 | 68 | 58 | pre-reorg, superseded by round_2 |
| round_2 | 22 | 196 | 167 | **no** - 1 of 102 implicated files touched since |
| round_3 | 6 (monitor) | 75 | 70 | **no** - 0 of 31 touched since |

Direct kimi-k3 corpus (`<results>/qc-kimi-k3/`):

| Round | Units | Findings | CONFIRMED | Integrated? |
|---|---|---|---|---|
| round_1 | 2 of 6 (shutdown) | 14 | 13 | abandoned - bundle moved under it, superseded |
| round_2 | 6 (common) | 32 | 27 | **yes**, 2026-07-25 - 21 of 22 implicated files touched; the 22nd is a rejected false positive |

**As of 2026-07-23 the five round_2 `common_part_*` units are fully integrated**
(all doc fixes plus the RTL defects they surfaced — arbiter_round_robin_simple
starvation, clock_pulse sizing, clock_gate_ctrl port ref, pwm repeat off-by-one;
see vault/Tasks/docs-review DOCREV-001 and vault/Tasks/common COMMON-012/COMMON-013). The
round_2 AMBA/monitor, math, shared and protocol units, and all of round_3, are
still un-integrated. Spot check against the RTL rather than commit dates:
`axi4_master_rd_mon_cg.md` still documents five clock-gating parameters that do
not exist (the RTL has only `CG_IDLE_COUNT_WIDTH`, gated at runtime by
`cfg_cg_enable`/`cfg_cg_idle_count`).

Beware the false positive that makes this look done: `92fbd051 docs(amba/monitor):
reconcile all monitor documentation with the RTL` landed 06:55 on 2026-07-22 and
reads like an integration pass. round_3 was sent at 13:06 **the same day** - it
reviewed the post-reconcile docs and still returned 70 confirmed defects. A
reconcile commit is not evidence that a round was applied; check the findings.

Retro-legacy (RLB) doc review was a separate effort with its own issue numbers
(#53, #59) and is not part of this corpus - no round contains RLB content.

Two critique layouts exist (`[CONFIRMED] title` with indented fields, and
`### F1` headings with bulleted fields). The indexer parses both; a parser that
handles only one silently undercounts the backlog, which reads as progress.

Related: [[doc-pipeline]] for how the reviewed Markdown becomes a deliverable.
