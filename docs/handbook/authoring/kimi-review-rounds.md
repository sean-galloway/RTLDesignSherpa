---
title: Kimi review rounds
summary: External doc review and humanization via Kimi - bundle, dispatch, rounds, and the five rules each failure taught.
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

## The five rules

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
5. **Verify every finding against the RTL before acting.** Reviewers report
   wrong things confidently when a unit was mis-packaged. *Case: the
   `math_subtractor` "five nonexistent modules" finding was our packaging bug,
   not the reviewer's error.*

## Endpoint

The key is never in a script. Locally the chain is
scripts -> litellm proxy on `localhost:4000` (dummy token `sk-x`) -> Moonshot,
with the real key behind the proxy. Anywhere else there is no proxy, so the
scripts read the endpoint from the environment instead:

| | `KIMI_BASE_URL` | `KIMI_API_KEY` | `KIMI_MODEL` |
|---|---|---|---|
| local | `http://localhost:4000/v1` (default) | `sk-x` (default) | `kimi-k2` (default) |
| direct | `https://api.moonshot.ai/v1` | real `MOONSHOT_API_KEY` | real Moonshot model id |

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

## State

Critiques are vendored into `docs/review/kimi/round_N/` (532 KB). The
`_bundle_snapshot/` inputs (11 MB) stay out - they are regenerable from git at
the reviewed commit. `bin/review/index_findings.py` flattens every critique
into `docs/review/kimi/FINDINGS.md`: per-round counts, the most-implicated
files, and a checkbox per finding.

| Round | Units | Findings | CONFIRMED | Integrated? |
|---|---|---|---|---|
| round_1 | 8 | 68 | 58 | pre-reorg, superseded by round_2 |
| round_2 | 22 | 196 | 167 | **no** - 1 of 102 implicated files touched since |
| round_3 | 6 (monitor) | 75 | 70 | **no** - 0 of 31 touched since |

**As of 2026-07-23 none of the accuracy findings have been integrated.** Two
spot checks confirm it against the RTL rather than against commit dates:
`axi4_master_rd_mon_cg.md` still documents five clock-gating parameters that do
not exist (the RTL has only `CG_IDLE_COUNT_WIDTH`, gated at runtime by
`cfg_cg_enable`/`cfg_cg_idle_count`), and `arbiter_round_robin_simple.sv` still
carries the rotate-direction defect round_2 flagged, unchanged since the initial
commit.

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
