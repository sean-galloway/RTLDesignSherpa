# TASK-014: Humanizer structural-preservation preamble + tag-survival test

> Migrated 2026-09-27 from `vault/Tasks/docs-review/closed.md` as **DOCREV-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-07-28 — tag-survival passed on the live cdc humanize round (0 links/anchors/captions lost in all 3 units; length ratios 0.97-1.08; apply_humanize length guard as second line). The structural preamble ships in run_batch.py's humanize prompt (including the unify-structure rule), and the fence/caption classes were verified on the real content before apply. DOCREV-003 unblocked.

**Addendum 2026-07-31 — the check is now a script, and the ad-hoc pass had a
hole.** `bin/review/check_tag_survival.py` does the comparison mechanically
(dropped pages, lost link targets, lost anchors, lost captions, unbalanced
fences, emoji, length ratio, heading drift) against the round's own
`_bundle_snapshot`. Re-running it over the already-applied cdc humanize round_3
found a class the hand check did not look for: **`apb5_slave_cdc.md` and
`apb5_slave_cdc_cg.md` had checkmark emoji INTRODUCED by the voice pass** (6 and
7 respectively), which the no-emoji rule exists to prevent because they break
the LaTeX path. Links, anchors and captions were indeed clean, exactly as
recorded — the pass was checked for what it was known to break.

The dropped-page class is why the script leads with it: `apply_humanize`
splits on `<!-- SOURCE FILE: ... -->` banners, so a banner the humanizer eats
folds that page into the previous one and it is never written. Nothing before
this compared the output's page set against the input's.

Gate order is now: `check_tag_survival.py` (refuse on FATAL) -> `apply_humanize
--dry-run` -> apply.

The owner-authored humanizer (`docs/kimi_humanization_style_guide.md`) governs
VOICE only; it says nothing about preserving Markdown structure. The final-round
brief must be the guide PLUS a structural-preservation preamble, written as a
wrapper rather than by editing the owner's guide.

**Already done:** `bin/review/run_batch.py` humanize mode sends DOCS-only (no
RTL) and its prompt carries an explicit preservation instruction. That covers
the mechanism; it does not cover the proof.

**Tag-survival test (2026-07-28, reset corpus): PASSED on cdc_meta** --
humanize round_1 returned the unit with structure fully intact (12/12
headings, 14/14 table rows, 41/41 links, 26/26 html tags, length ratio
1.02). cdc_meta has no code fences or captions, so the fence/caption classes
are verified by the same structural diff on the FULL cdc area round before
applying (apply_humanize refuses dramatic shortening as a second guard).
Do not run across the corpus first: the docs are the
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
