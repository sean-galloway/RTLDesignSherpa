<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Open (accepted, not started)

---

## DOCREV-010 — every docs/markdown book needs index.md + overview.md
**Status:** open 2026-07-25 (Sean)
**Priority:** P2

**The rule** (recorded in [[doc-placement]]): every directory under
`docs/markdown/` carries BOTH `index.md` (the catalogue) and `overview.md` (the
orientation), and the overview links to the index. `assets/` is exempt -- it is
shared header fragments and image dirs, not a book.

**Gaps as of 2026-07-25:**

| Book | index.md | overview.md |
|---|---|---|
| RTLAmba, RTLCommon, projects | yes | yes |
| RTLMath | yes | **write it** |
| Scripts | yes | **write it** |
| TestTutorial | yes | **write it** |
| RTLcdc | **write it** | **write it** |

`docs/markdown/RTLcdc/` exists but is EMPTY, and its casing disagrees with the
`docs/markdown/RTLCdc/` that AMBA-CDC-REORG specifies. Settle on one name when
that book is populated -- do not end up with both. That book is blocked on the
CDC reorg anyway, since its pages have to move out of RTLCommon/RTLAmba first.

**Also: the link back from the RTL tree.** Each area's RTL should point at its
book's `overview.md`. It cannot be a `README.md` (banned under `rtl/`, commit
`f7ca848a`), so use the two allowed anchors:
- the `// Documentation:` module header line -- already in 225 of 232 modules
  under `rtl/{common,cdc,math}`, but most point at `index.md`; repoint to
  `overview.md`, and note 113 math modules point at `IEEE754_ARCHITECTURE.md`
  and 12 at `BF16_ARCHITECTURE.md`, which want checking separately;
- the area `CLAUDE.md` -- exists only for `rtl/amba` and `rtl/common`;
  `rtl/cdc`, `rtl/math` and `rtl/integ_amba` have none.

**Why it matters beyond tidiness:** `build_review_bundle.py` builds a unit per
`_book_*_index.md` and includes `overview.md` plus the pages that index links.
A book with no overview reviews less than it appears to, and `index.md` /
`quickstart.md` are outside the bundle entirely -- which is how RTLCommon's meta
docs kept a wrong module count, six relocated modules and a phantom `sync_2ff`
through three review rounds. Pair this with the `<area>_meta` unit from
DOCREV-009.

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

---

## DOCREV-009 — Final per-section correctness + humanization pass (whole repo)
**Status:** open 2026-07-24 — the closing gate for the doc effort
**Priority:** P2
**Owner:** TBD

Supersedes and absorbs the earlier "final Kimi round" (DOCREV-008). After every
area's findings are integrated and the reorg has settled, do ONE comprehensive
closing pass, **section by section**, across the entire repo — `rtl/*`,
`docs/markdown/RTL*`, **and** `projects/*` when we get there.

**Per section, send EVERYTHING — not just module pages:**
- [ ] Every `.md` in the section: `index.md`, `README.md`, `overview.md`,
      `quickstart.md`, the per-module pages — plus the section's RTL. The
      earlier rounds bundled module-page + RTL only; the meta-docs (index/
      readme/overview) were never reviewed and are exactly where count/structure
      drift hides (see the rtl/common 86-vs-55 case, [[doc-placement]] rule 3).
- [ ] **Correctness check** (`qc`): bundle from the CURRENT tree so paths are
      post-split (RTLMath, moved READMEs), serial, large max_tokens
      ([[kimi-review-rounds]] rules 1-4). Measure results against the tree;
      anything CONFIRMED becomes new DOCREV work. A near-empty round is the goal
      — that is the evidence the backlog is actually closed.
- [ ] **Humanization** (`humanize`) of ALL md files in the section — index,
      readme, overview, module pages — not only the prose docs. This is the
      bulk README humanization from DOCREV-007 folded in: every md, every
      section. Tooling gap to close first: `run_batch.py humanize` only globs
      `books/**/DOCS.md`, so index/readme/overview and scattered READMEs need
      bundling or a humanizer that targets them directly.

**Order:** correctness first, humanization second — never humanize an
un-corrected doc (the voice pass is prose-only and must not be handed known-wrong
content to "improve"). Run it section by section so a bad section is contained,
not smeared across one giant round.

**Gate:** do not start until common ✅, cdc ✅, math ✅, shared, apb/axi*, and
monitor (round_3, 70 CONFIRMED) are all integrated, AND the README rollout
(DOCREV-007) is done so the md set is stable. Needs Kimi enablement (DOCREV-005)
off-workstation.