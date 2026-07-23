---
name: review-rounds
description: External doc-review rounds (Kimi) - bundle building, serial dispatch, round protection, token budgets, findings triage, and the humanization pass. Use when sending docs for critique, triaging findings, or running the humanizer.
---

# review-rounds

READ FIRST: docs/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: docs/handbook/authoring/kimi-review-rounds.md - the five rules,
both round modes, and the endpoint config. Voice pass: [[humanization-voice]].
Off-workstation runs: [[cloud-sandbox]].

Scripts: bin/build_review_bundle.py (rebuild ALL units, always) then
bin/review/run_batch.py {qc|humanize} (serial, never overwrites a round).

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
