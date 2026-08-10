---
title: Humanization voice
summary: The persona and LLM-ism banlist used for the final prose pass; what the pass may and may not change.
---

# Humanization voice

The full persona, language rules and LLM-ism banlist live in
`docs/kimi_humanization_style_guide.md`. That file is loaded verbatim as the
system brief for a `humanize` round ([[kimi-review-rounds]]) - it is the
artifact, not a summary of one. Edit it there; do not restate it here.

What the note records is the contract around it.

## The pass may change prose only

Every technical claim, number, signal name, code block, table, heading and
cross-reference survives byte-identical. The prompt says so explicitly, and it
has to: a model handed documentation and told to "improve" it will quietly
round a timing number or rename a signal to something it finds more natural.

This is also why the humanize round is sent **without RTL**. Ground truth in
the context turns a rewrite request into a review - you get findings back when
you asked for a draft.

## Verify tag survival before trusting a round

The docs carry structure the downstream pipeline depends on - caption encoding
for LoF/LoT/LoW, page-path comments, book anchors ([[doc-pipeline]]). A voice
pass can eat those without saying anything. **`bin/review/check_tag_survival.py`
is the gate**; run it before `apply_humanize`, on every round:

    python3 bin/review/check_tag_survival.py --results <humanize round dir>

It diffs each rewritten page against the round's own `_bundle_snapshot`. FATAL
(do not apply): a dropped page, a lost link target or anchor, a lost caption
line, unbalanced code fences, an emoji introduced. WARN (judgement): heading
drift and length ratios outside 0.85-1.20, both of which the unify-structure
instruction produces legitimately.

**The dropped-page class is the one that hides.** `apply_humanize` splits the
returned blob on `<!-- SOURCE FILE: ... -->` banners, so a banner the humanizer
eats folds that page into the previous one: the page is silently never written,
the round reports success, and the book loses a chapter. Comparing the output's
page set against the input's is the only thing that catches it.

*Case: the check was done by hand for the 2026-07-28 cdc round and recorded as
clean - correctly, for links, anchors and captions, which is what it looked at.
Re-running the script over that same applied round found checkmark emoji
INTRODUCED into `apb5_slave_cdc.md` and `apb5_slave_cdc_cg.md`. A hand check
finds the classes you already know about; that is the argument for the script,
not for a more careful hand check.*

## No emojis

They break the LaTeX path in PDF generation and read as unprofessional in
formal documentation. The banlist covers this; it is repeated here because it
is the rule most often violated by a generative rewrite.

## Beside-code READMEs are in scope

The voice guide binds authored beside-code READMEs, not only the Kimi-bundled
module pages. A README stub is *written* in voice from the template in [[doc-placement]] so
it starts human, and it is ALSO subject to the eventual bulk humanization pass
over all READMEs (DOCREV-007) - writing-in-voice is the floor, not an exemption.
The no-emoji / no-LLM-ism / plain-declarative rules bind a README identically to
a module page. Guide content that moves from a bloated README into
`docs/markdown/` becomes bundle-able and picks up the normal pass too.

## Unify formatting and structure as you go (Sean, 2026-07-28)

The voice pass ALSO normalizes presentation across the area's pages: one
heading style and hierarchy, one table style per table kind (parameter, port,
latency), one section ordering per page kind -- the book should read as one
document, not pages written years apart. **Worked examples are exempt:**
step-by-step walkthroughs (waveform analyses, reset scenarios, numeric
traces) keep their didactic structure; forcing those into the uniform mold
destroys how they teach. Pipeline structure still survives byte-identical
(captions, anchors, link targets) -- unification is cosmetic, never
structural in the machine-readable sense. Carried in the run_batch.py
humanize prompt wrapper, not the owner's style guide.

## The no-emoji rule was never in the prompt (2026-08-10)

It was written down in three places that the model never sees: this note, the
`db18b03b` sweep commit, and the reviewer's own head. The humanize wrapper in
`run_batch.py` carried the *unify structure* instruction and said nothing about
emoji, and `kimi_humanization_style_guide.md` -- the brief actually sent -- was
a pure voice guide.

So the gaxi round came back having ADDED 20 glyphs (81 -> 101) across three
pages, and `check_tag_survival.py` failed it with 3 FATAL. Every one of the 81
pre-existing glyphs survived too, which is the same thing `db18b03b` observed on
common: **the humanizer treats emoji as content and removes none.** A voice pass
can never be the thing that cleans them up.

Both rules now live where the model reads them -- the emoji prohibition with its
per-glyph replacement table, and a canonical `##` section list, in the style
guide, with a short form repeated in the wrapper. "Unify the headings" without
naming the target set had let the model invent its own self-consistent scheme
each round.

The lesson generalizes past emoji: **a rule the pipeline enforces at the gate
but never states in the prompt is a rule you have chosen to catch instead of
prevent.** The gate is the backstop, not the specification.

Related: [[kimi-review-rounds]], [[doc-pipeline]], [[module-doc-template]].
