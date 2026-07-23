---
name: review-rounds
description: External doc-review rounds (Kimi) - bundle building, serial dispatch, round protection, token budgets, findings triage (doc-fix vs RTL-fix), measuring integration status rather than trusting commit history, verifying fixes with clean rebuilds + mutation checks, and the humanization pass. Use when sending docs for critique, triaging findings, or running the humanizer.
---

# review-rounds

READ FIRST: docs/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: docs/handbook/authoring/kimi-review-rounds.md - the seven rules,
both round modes, and the endpoint config.

Three that bite hardest when triaging findings:
- A finding that reads like a doc nit can be a real RTL defect (and vice
  versa). Read the whole finding, not the headline; triage doc-fix vs RTL-fix
  per finding.
- Integration status is MEASURED against the tree, never inferred from commit
  history. A "reconcile docs with the RTL" commit is not evidence a round was
  applied - one landed six hours before a round that then found 70 confirmed
  defects.
- Verify a fix with a CLEAN REBUILD and mutation-check the test: a stale
  sim_build passes against the old RTL, and a test whose stimulus cannot expose
  the bug passes against the broken RTL. Revert, confirm RED, restore.

Voice pass: [[humanization-voice]]. Off-workstation runs: [[cloud-sandbox]].

Scripts: bin/build_review_bundle.py (rebuild ALL units, always) then
bin/review/run_batch.py {qc|humanize} (serial, never overwrites a round).

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
