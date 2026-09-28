# TASK-004: Final MD-only humanize round

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** open 2026-07-23 — blocked on DOCREV-002

Sequencing is deliberate: accuracy rounds first (DOCS + RTL, so the reviewer has
ground truth), humanize LAST. Rewriting prose over stale content only makes
wrong statements read more fluently — so this is also blocked on DOCREV-001.

Run with `bin/review/run_batch.py humanize`. The docs-only path DOCREV-002 asked
for already exists there; the bundler still emits `RTL.sv` per unit, which
humanize mode simply does not send.
