<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Open (accepted, not started)

---

## DOCREV-011 — fix ALL broken links, whenever they were introduced
**Status:** open 2026-07-26 (Sean); mechanical classes swept 2026-07-27
**Priority:** P2

Not a rename cleanup. **Every** broken link in the repo, no matter which move,
split or deletion caused it. First measured 2026-07-26 at `d65be489`: **495
broken links across 160 files.**

### Where it stands

**374 remain, across 146 files** (re-measured 2026-07-27 at `057f75df`+). The
two mechanical classes were swept outside `projects/`, which is what closed the
121:

| n | class | how to fix |
|---|---|---|
| 308 | target does not exist anywhere | judgement call each: write the page, repoint, or delete the link |
| 64 | target moved (same filename exists elsewhere) | mechanical, but these are the ones the sweep deliberately skipped -- see below |
| 2 | repo-root-relative | mechanical |

**262 of the 374 are under `projects/`**, which is deferred. Outside projects the
remaining count is 112, and it is dominated by pages that reference documentation
that was never written:

| n | file |
|---|---|
| 24 | `bin/markdown_to_word_instructions.md` |
| 10 | `bin/TBClasses/wavedrom_user/GAXI_WAVEDROM_GUIDE.md` |
| 10 | `docs/markdown/TestTutorial/wavedrom_gaxi_example.md` |
| 7 | `bin/DOC_GENERATION.md` |
| 6 | `docs/markdown/overview.md` (was 76) |
| 5 | `docs/DOCUMENTATION_STANDARDS.md` |

`README.md` and `docs/markdown/rtl-cdc/cdc.md` are now at zero.

### What the sweep deliberately would not touch

Three exclusions, each because a "fix" there would be a corruption:

- **`docs/review/`** — archived reviewer output. It *quotes* what a page said at
  the time. Rewriting a quoted link falsifies the record.
- **Anything inside a ``` fence** — templates and examples. The link in
  `assets/*/DIAGRAM_PLAN.md` or in `doc-placement.md` is written relative to the
  *page being generated*, not to the file it appears in. An automated pass
  "fixed" both on the first attempt and had to be reverted.
- **`projects/`** — deferred by request until the rest of the tree is done.

That accounts for most of the 64 remaining "moved" links. Any future automated
pass must keep these three exclusions.

**Plus a second, separate class: 126 `rtl/**/*.sv` `// Documentation:` headers
point at a file that does not exist** -- 113 at `IEEE754_ARCHITECTURE.md`, 12 at
`BF16_ARCHITECTURE.md`, 1 at `docs/bf16-research.md`. These are bare filenames,
not paths, so they never resolved from anywhere; they want a real
`docs/markdown/rtl-math/...` target (see DOCREV-010, which wants the same
headers pointed at each area's `overview.md`).

### Regenerate the list

    python3 - <<'EOF'
    import os, re, subprocess
    files=[f for f in subprocess.check_output(['git','ls-files','*.md'],text=True).split()
           if os.path.isfile(f)]
    lr=re.compile(r'\[[^\]]*\]\(([^)\s]+?)(?:#[^)\s]*)?\)')
    for f in files:
        root=os.path.dirname(f) or '.'
        for m in lr.finditer(open(f,encoding='utf-8',errors='ignore').read()):
            t=m.group(1)
            if t.startswith(('http://','https://','mailto:','#')): continue
            if not os.path.exists(os.path.normpath(os.path.join(root,t))):
                print(f"{f} -> {t}")
    EOF

### Notes before starting

- **`docs/review/kimi/**` was removed in the 2026-07-28 corpus reset** — its
  4 broken links went with it (they were inside critique artifacts, which are
  evidence and were never to be hand-edited anyway, [[doc-placement]] rule 5).
- **Dangling `[[wikilinks]]` in `vault/` are not broken links.** The handbook
  convention is that a `[[name]]` with no note yet marks something worth
  writing. 36 distinct ones exist; leave them.
- Do the two mechanical classes (221 of 495) first and re-measure. That leaves
  the 274 judgement calls, which is where the real work is -- and some of those
  will be "the page should exist", which turns into writing, not linking.
- **Wire the checker into a gate afterwards, or this returns.** Nothing runs it
  today, which is exactly how 495 accumulated. Same gap as
  `filelist_registry.py --check` (see [[filelists]]).

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
| rtl-amba, rtl-common, projects | yes | yes |
| rtl-math | yes | **write it** |
| Scripts | yes | **write it** |
| TestTutorial | yes | **write it** |
| RTLcdc | **write it** | **write it** |

`docs/markdown/RTLcdc/` exists but is EMPTY, and its casing disagrees with the
`docs/markdown/rtl-cdc/` that AMBA-CDC-REORG specifies. Settle on one name when
that book is populated -- do not end up with both. That book is blocked on the
CDC reorg anyway, since its pages have to move out of rtl-common/rtl-amba first.

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
`quickstart.md` are outside the bundle entirely -- which is how rtl-common's meta
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
every tag class at once. `docs/markdown/rtl-amba/cdc/cdc.md` and the math pages
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
**Status:** open 2026-07-23 — **updated 2026-07-28 for the corpus reset**

The pre-reset collateral now lives at
`~/rtl-doc-review/archive-pre-reset-2026-07-28/` (untracked, one disk): the
old results tree (proxy corpus inputs + k3 rounds 1-10) and the run logs.
That archive is the FP-rate baseline for DOCREV-012 and the only copy of the
old critiques outside git history. Decide: keep, prune, or delete once the
reset corpus has its own track record. The active pipeline's collateral
(`~/rtl-doc-review/books/`, fresh `results/`) is regenerable or current work
product; same rule — do not leave anything as the only copy on one disk.

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

**Not a blocker on the workstation.** Direct-mode rounds run fine here (the
reset cdc round is the proof case); this gates only rounds run from a cloud
sandbox.

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
then its README, the same order used for the rtl-math move.

---

## DOCREV-009 — Final per-section correctness + humanization pass (whole repo)
**Status:** open 2026-07-24 — the closing gate for the doc effort.
**Subsumed 2026-07-28 by AUDIT-001** (`vault/Tasks/site-audit/`): parts 2-3 of
the site-wide audit are this task, widened with RTL correctness (part 1) and
verification coverage (part 4). When AUDIT-001 goes active, cut this block
there; until then this remains the detailed statement of the docs half.
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
      post-split (rtl-math, moved READMEs), serial, large max_tokens
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

**Gate:** do not start until the DOCREV-013 per-area rounds (cdc, common,
math, amba, projects/components) are done, AND the README rollout
(DOCREV-007) is done so the md set is stable. Needs Kimi enablement
(DOCREV-005) off-workstation. (Pre-2026-07-28 this gate listed the old
backlog areas; the corpus reset replaced backlog integration with the
DOCREV-013 fresh rounds.)
## DOCREV-013 — Fresh per-area qc rounds under the adjudication pipeline
**Status:** open 2026-07-28
**Priority:** P1
**Owner:** TBD

The corpus reset (2026-07-28) cleared every prior round; this task is the
replacement for backlog integration (DOCREV-001, dropped). Each area gets a
fresh qc round under the tightened REVIEWER_BRIEF, adjudicated by
`verify_findings.py` (validated 2026-07-28 on cdc round_1, DOCREV-012).

**Area order (Sean, 2026-07-28):** cdc, common, math, amba (broken down
further when we get there), projects/components (also broken down when we
get there). After those, assess whether the fpga-specific areas need it.

**Per-area startup checklist** (Sean, 2026-07-28 — the Makefile step is part
of starting each area, not optional prep):

1. **Four-line Makefiles.** The RTL area gets the four-line Makefile
   delegating to `rtl/make/area.mk` (lint/etc. over
   `filelists/$(AREA)_all.f`); the val area gets the four-line Makefile
   delegating to `make/tests.mk` (clean-all + glob-discovered test running,
   TOOL-008). Already in place for cdc/common/math/amba/integ_*; CHECK when
   each new area starts — projects/components areas will need them added.
2. Rebuild the WHOLE bundle from the current tree (rule 1), then regenerate
   the area's `_meta` unit immediately — the bundler deletes it. Then run
   `bin/review/augment_golden_deps.py` on the area's PART units (never the
   `_meta` unit — its RTL.sv is an inventory): doc-referenced but
   non-instantiated modules (reset_sync class) join the bundle as GOLDEN
   ground truth — evidence for claims docs make about them, never finding
   targets (Sean, 2026-07-28; the reset_sync REFUTED-a-real-finding case).
3. qc round for the area, serial, large max_tokens (rules 2-4).
4. Adjudicate the round's findings with `bin/review/verify_findings.py`,
   then human-triage what the verifier does not REFUTE.
5. Integrate; re-round until near-empty — the near-empty round is the
   evidence. Humanize only after correctness is clean.

One area at a time, to completion — the multitasking failure (nothing gets
fixed while a second area runs) is documented in [[kimi-review-rounds]].

### Progress log — DOCREV-013

**cdc (rounds 1-2, 2026-07-28).** round_1: 3 findings, 0 FP, all doc-only
(SYNC_STAGES->N_FLOP_CROSS, 1.25x->1.2x, duplicate `r_q_array` declaration) —
fixed, and DOCREV-012 validated the adjudication pass on them. Confirmation
round_2: 5 findings; triage + verifier: **4 real, 1 FP** (overview.md
"omission" was a non-exhaustive sentence, correct REFUTED). The 4: cdc.md
reset table 4-phase cell (prose said "repeated or dropped"), skid_buffer doc
missing the `DW = DATA_WIDTH` alias line, `reset_sync #(.STAGES(3))` +
`.async_rst_n` example against a module whose params are `N`/`rst_n` (the
verifier REFUTED this one on absent-file grounds — VERIFIER_BRIEF rule 4 now
makes absent-cited-file an automatic UNCERTAIN), johnson2bin "emptying from
the left" vs its own "from the right" (RTL confirms right). All fixed. No RTL
changes in either round.
