<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# nexysa7 tasks — dropped

<!-- Moved from vault/Tasks/amba/ 2026-09-14: a NexysA7 flow task, filed under amba -->
## NEXYSA7-STREAM-MON-SPLIT — WITHDRAWN, this was my own tooling bug
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
