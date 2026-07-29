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
pass can eat those without saying anything. Diff a rewritten unit against its
snapshot in `_bundle_snapshot/` and confirm the tags are still there before
accepting the round.

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
