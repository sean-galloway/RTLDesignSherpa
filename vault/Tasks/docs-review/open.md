<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Open (accepted, not started)

---

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

---

## DOCREV-007 — README rollout: convert 105 beside-code READMEs to link stubs
**Status:** open 2026-07-24 — pattern established (rtl/common), 104 to go
**Priority:** P2
**Owner:** TBD

The tree has **105 `README.md` files**, and many are 500-1000 line standalone
guides beside the code — `projects/components/README.md` (1062),
`converters/README.md` (719), `rtl/integ_amba/examples/README.md` (698),
`rtl/amba/README.md` (635). Every one is a second copy that rots on the next
structural change, exactly as `rtl/common/README.md` did (claimed 86 modules
after the split left 55). See [[doc-placement]].

**The pattern, already worked once (rtl/common, commit ec6bd81a):**
- [ ] For each big README: move the genuine standalone-guide prose into
      `docs/markdown/<Book>/` (a `quickstart.md` or folded into `index.md`),
      correcting staleness during the move (derive counts, drop content that
      moved elsewhere).
- [ ] Replace the beside-code `README.md` with a link stub, written in voice
      from the template in [[doc-placement]].
- [ ] Repoint referrers (the `# Documentation:` code headers, cross-links).
- [ ] Link-check the moved tree.

**Humanization (Sean, 2026-07-24): every README gets humanized eventually.**
Two phases:
- [ ] **Write in voice now.** Each stub is authored from the [[doc-placement]]
      template in voice, so it starts human. This is the floor.
- [ ] **Bulk humanization pass over ALL READMEs, later.** The stubs included,
      not only the guide prose they shed. This is a real pass, still to be run.
      **Tooling gap:** `bin/review/run_batch.py humanize` only globs
      `books/**/DOCS.md`, so it cannot see scattered `README.md` files today.
      Running the bulk pass means either bundling the READMEs as units or
      teaching the humanizer to target `README.md` directly — decide which as
      part of this task.

Guide content that moves into `docs/markdown/` becomes a bundle-able `DOCS.md`
unit and gets the normal humanize pass with every other page as a side effect.
Contract recorded in [[humanization-voice]] and [[doc-placement]].

**Do not blanket-convert.** Some READMEs legitimately stay: `known_issues/README.md`
is a bug-record index, `boards/README.md` and report-dir READMEs may be local
manifests the tooling or a human genuinely reads in place. Apply the
[[doc-placement]] test (method/second-copy vs local-instruction) per file, not a
mass `sed`.

**Sequence with the doc reviews.** Converting a README that a pending Kimi unit
cites would move the target mid-review; do the area's DOCREV-001 findings first,
then its README, the same order used for the RTLMath move.
