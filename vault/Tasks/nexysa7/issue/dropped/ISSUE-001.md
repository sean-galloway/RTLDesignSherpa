# ISSUE-001: MON-SPLIT — WITHDRAWN, this was my own tooling bug

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/dropped.md` as **NEXYSA7-STREAM** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** DROPPED 2026-08-28, same day it was filed
**Priority:** n/a -- there was never a defect here

Filed claiming `flows-stream-monitor`'s filelists still pointed into
`flows-stream-bridge` (9 dangling refs), and attributed to an unfinished move
by another session. **That was wrong, and the fault was in the checker, not the
filelists.**

Those filelists reference `$STREAM_CHAR_ROOT`, which every flow Makefile
exports as its OWN directory (`export STREAM_CHAR_ROOT := $(SELF_DIR)`).
`filelist_registry.ROOT_VARS` pinned it to flows-stream-bridge, so the checker
expanded monitor-flow paths against the bridge flow and reported seven
perfectly good references as broken. Under `make`, they always resolved.

Fixed in ecdf5a3e by harvesting per-flow values instead of pinning one;
`--resolve` now expands the monitor-flow harness correctly for the first time,
and `nexys_stream_char` reports 0 broken refs.

Worth keeping as the record of the failure mode: a static resolver that guesses
one value for a per-flow variable does not find bugs, it manufactures them --
and I nearly left a correct tree flagged as broken on the strength of it.
