---
name: review-rounds
description: External doc-review rounds (Kimi) - bundle building, serial dispatch, round protection, token budgets, findings triage, and the humanization pass. Use when sending docs for critique, triaging findings, or running the humanizer.
---

# Review rounds + humanization

Canonical process doc: /mnt/data/github/rtl-doc-review/KIMI_REVIEW_HOWTO.md
(key location, scripts, round layout). Results live OUTSIDE the repo in
rtl-doc-review/results/<model>/round_N/ - never overwritten, inputs
snapshotted per round.

Process rules (each learned expensively):
1. Rebuild ALL bundles (bin/build_review_bundle.py), select at SEND time.
2. Serial dispatch only.
3. Never overwrite a round.
4. Kimi reasoning eats the completion budget: 32768 -> 65536 auto, 131072
   manual for giant units; still truncating = split the unit in the bundler.
5. Verify findings against RTL before acting - bad packaging produces
   confident wrong findings (a reviewer once "found" five nonexistent
   modules because the bundler mis-packaged the unit).

Humanization (final round, MD-only, no RTL):
- Style guide: docs/kimi_humanization_style_guide.md (persona, voice rules,
  LLM-ism banlist). It governs VOICE only.
- Wrap it with a structural-preservation preamble: prose only - never touch
  headings, LoF/LoT/LoW caption encodings, cross-links, code fences,
  identifiers, tables, asset paths; no emojis (LaTeX pipeline).
- Gated on the tag-survival test: run one heavily-marked-up page through,
  diff structure, regenerate the affected book PDF, confirm ToC/lists/xrefs
  unchanged. See rtl-doc-review/REVIEW_TODOS.md items 1-2.
