<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Open (accepted, not started)

---

## DOCREV-001 — Integrate the 271 outstanding Kimi accuracy findings
**Status:** open 2026-07-23 — nothing integrated yet

round_2 (196 findings, 167 CONFIRMED) and round_3 (75 findings, 70 CONFIRMED)
are un-integrated. Verified by measurement, not by reading commit history:
round_2 has 1 of 102 implicated files touched since the review, round_3 has 0
of 31, and two findings were re-checked against the RTL directly —
`axi4_master_rd_mon_cg.md` still documents five clock-gating parameters that do
not exist, and `arbiter_round_robin_simple.sv` still carries the
rotate-direction defect (unchanged since the initial commit).

Critiques and a checkbox index: `docs/review/kimi/` (`FINDINGS.md` leads with a
most-implicated-files table, which is the work-planning view).

**Trap to avoid:** `92fbd051 docs(amba/monitor): reconcile all monitor
documentation with the RTL` landed 06:55 on 2026-07-22 and reads like an
integration pass. round_3 was sent at 13:06 the same day, reviewed the
post-reconcile docs, and still returned 70 confirmed defects. A reconcile
commit is not evidence a round was applied.

**Not all of these are doc bugs.** Several are RTL defects surfaced by
documentation review (the arbiter rotate direction is the clearest). Triage
into doc-fix vs RTL-fix before batching the work, and file the RTL ones in the
owning area's task page.

Per handbook rule 5 ([[kimi-review-rounds]]): verify each finding against the
RTL before acting. Reviewers report wrong things confidently when a unit was
mis-packaged.

round_1 (68 findings) is pre-reorg and superseded by round_2 — do not work it.

## DOCREV-002 — Humanizer structural-preservation preamble + tag-survival test
**Status:** open 2026-07-23 — partially implemented; gates DOCREV-003

The owner-authored humanizer (`docs/kimi_humanization_style_guide.md`) governs
VOICE only; it says nothing about preserving Markdown structure. The final-round
brief must be the guide PLUS a structural-preservation preamble, written as a
wrapper rather than by editing the owner's guide.

**Already done:** `bin/review/run_batch.py` humanize mode sends DOCS-only (no
RTL) and its prompt carries an explicit preservation instruction. That covers
the mechanism; it does not cover the proof.

**Still to do — the tag-survival test.** Send a SMALL test bundle and verify
nothing structural is lost. Do not run across the corpus first: the docs are the
source for the PDF book pipeline, so a prose rewrite that drops markup silently
breaks book generation, and that will not be obvious from reading the prose.

Diff before/after and confirm all of these survive:
- heading hierarchy (levels and order — the ToC is generated from it)
- caption encoding for LoF / LoT / LoW. Encoded in captions, NOT via flags
  ([[doc-pipeline]]). Losing them silently empties those lists.
- cross-links between pages (index files follow links recursively; md_to_docx
  walks them to assemble a book)
- fenced code blocks and their language tags
- inline identifiers: signal names, module names, parameters, file:line refs
- tables (pipe alignment)
- image/asset paths (WaveDrom/mermaid assets are referenced by path)
- NO EMOJIS introduced — hard repo rule, they break the LaTeX/PDF path

**Suggested bundle:** one small page with heavy markup beats a large plain one.
A page with a figure + table + waveform + code block + cross-links exercises
every tag class at once. `docs/markdown/RTLAmba/cdc/cdc.md` and the math pages
with rendered tables are good candidates.

**Acceptance:** regenerate the affected book to PDF after the test rewrite and
confirm ToC, LoF/LoT/LoW and cross-references are unchanged. Prose differs;
structure does not.

Reference implementation exists: RTLDesignSherpa-DV already ran this pass
(`d910c34 build: humanizer structural preamble + docs-only bundler mode`,
`da69788 docs: humanize all component and scoreboard pages (kimi round_2)`).
Port the preamble rather than re-deriving it.

## DOCREV-003 — Final MD-only humanize round
**Status:** open 2026-07-23 — blocked on DOCREV-002

Sequencing is deliberate: accuracy rounds first (DOCS + RTL, so the reviewer has
ground truth), humanize LAST. Rewriting prose over stale content only makes
wrong statements read more fluently — so this is also blocked on DOCREV-001.

Run with `bin/review/run_batch.py humanize`. The docs-only path DOCREV-002 asked
for already exists there; the bundler still emits `RTL.sv` per unit, which
humanize mode simply does not send.

## DOCREV-004 — Back up or retire the off-repo review collateral
**Status:** open 2026-07-23

`/mnt/data/github/rtl-doc-review/` is untracked on a single disk. The critiques
have been vendored into `docs/review/kimi/` and the process into the handbook,
so what remains there is:

- `books/` + `results/*/round_N/_bundle_snapshot/` (~22 MB) — regenerable from
  git at the reviewed commit, so arguably disposable.
- `bin/dispatch_review.py`, `send_kimi_round.py`, `redispatch_big.py` —
  superseded by `bin/review/run_batch.py` (which folds in the 131072 rung that
  `redispatch_big` existed to provide manually). Retire once a round has been
  run successfully through the new path.

Decide: delete, or move under a tracked location. Do not leave it as the only
copy of anything.

## DOCREV-005 — Enable Kimi from the cloud (key + egress)
**Status:** open 2026-07-23 — prerequisite for running any new round off the workstation

The scripts are endpoint-agnostic ([[kimi-review-rounds]]), but two things
outside the repo have to be arranged before a cloud round can run:

- [ ] **Key as a sandbox secret.** `MOONSHOT_API_KEY` lives in
      `/mnt/data/github/seans-cli-ai-local/config/frontier-keys.env`, untracked
      on one disk. Set it in the cloud environment's secret store as
      `KIMI_API_KEY` — pasted into the secret settings, never into a file, never
      committed, never on removable media. Also set
      `KIMI_BASE_URL=https://api.moonshot.ai/v1` and `KIMI_MODEL=kimi-k3`
      (`kimi-k2` is the local proxy alias and 404s against Moonshot directly).
- [ ] **Egress.** Sandboxes filter outbound network; `api.moonshot.ai` may need
      allowlisting. If the first call hangs or 403s, that is the cause — nothing
      in the scripts can work around it.
- [ ] Confirm the model id is accepted. `kimi-k3` is what `litellm-config.yaml`
      routes to, but no live direct call has been made to verify Moonshot takes
      it unprefixed. `GET /v1/models` with the real key lists the valid ids.

**Not a blocker for the backlog.** DOCREV-001 is 339 findings of already-paid-for
text sitting in `docs/review/kimi/`; none of it needs an API call. This gates
only *new* rounds (DOCREV-003).
