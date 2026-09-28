# TASK-007: Every module MUST have a filelist and a registry entry

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-010** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 (168faeaa) — all five items done; two had an
expired premise. Re-verified 2026-09-01: `bin/filelist_registry.py --check`
returns PASS across every area.

**The rule** (authority: [[filelists]]): every module in `rtl/common/` has a
filelist in `rtl/common/filelists/`, and the area is registered in
`bin/filelists.toml`. A new module lands with its `.f` **in the same commit** —
not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state is good but unenforced.** `bin/filelist_registry.py --check`
reports common at 57 modules / 55 covered / 0 uncovered. The 2-module gap is
the `[exempt]` ledger, not a hole:

- `fifo_sync_multi` — multi-instance wrapper; no consumer yet
- `fifo_sync_multi_sigmap` — multi-instance wrapper; no consumer yet

**Work:**
1. Resolve the two exemptions: give each a filelist and a consumer, or drop the
   module. "No consumer yet" is a debt entry, not a permanent state.
2. Wire `--check` into a gate. **Nothing runs it today** — not the pre-commit
   hook, not CI (the only workflow is `track-clones.yml`), not a Makefile
   target. A MUST that nothing enforces is a wish. Shared with AMBA TASK-026;
   do the gate once for both.
3. When reading `--check` output, read all three numbers. It prints `PASS` when
   `declared - covered - exempt` is empty, so "55 covered" alongside "0
   uncovered" on a 57-module area is expected and still worth checking.

**CLOSED 2026-08-09 — all three work items satisfied, two of them by other
work rather than by anyone doing this task.**

1. **The two exemptions are gone.** `[exempt]` no longer lists
   `fifo_sync_multi` or `fifo_sync_multi_sigmap`, and common carries zero
   exemptions today.
2. **`--check` IS gated now.** `.github/workflows/filelist-checks.yml` runs
   `--check`, `--audit` and `--blindspots` on every PR, the first two as hard
   gates. The task was written when the only workflow was `track-clones.yml`.
3. **The numbers read cleanly:** 46 modules / 46 covered / 0 uncovered / 0
   broken refs. (46, not the 57 recorded here: `math_*` split out to
   `rtl/math`, then `mod_3_compress` followed it, and `sync_pulse` and
   `glitch_free_n_dff_arn` moved to `rtl/cdc`.)

**Worth naming why it stayed open**: nothing was wrong with the task, and
nothing here was hard. Its premise -- "current state is good but unenforced"
-- simply stopped being true, and no signal exists that retires a task when
the world catches up with it. It was the only item on the open list that was
already done, which made the remaining work look larger than it was. Re-read
the premise of a long-lived task before working it; the answer is sometimes
that it is finished.


---
