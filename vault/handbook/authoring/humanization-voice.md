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
