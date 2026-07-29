<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — closed (done)

### TASK-059: Fix STREAM extended chained strided (transpose) descriptor corruption

**Priority:** High
**Status:** [x] Done (2026-07-29) — fixed + regression-tested.

**Bug record:** `projects/components/dmas/stream/known_issues/resolved/extended_chained_transpose.md`

**Symptom:** With `USE_ROW_COL_MAJOR_ADDRESSING=1`, a strided/per-beat extended
(transpose) descriptor reached via `next_ptr` **chaining** read the wrong source,
wrote with holes, and corrupted the **preceding** descriptor's last-touched beat.
Silent — no error raised. Directly-kicked transpose and chained
extended-**contiguous** both passed; only *chained + strided* failed.

**Root cause:** the run-base generator start pulse `w_addrgen_start` fired for
EVERY descriptor. A LEGACY descriptor ran `stream_run_addr_gen` with its own base
and the STALE `r_descriptor_ext` strides, pushing bogus run-bases into the
generator's internal prefetch FIFO (`gaxi_fifo_sync`, no flush). Legacy never
consumes run-bases, so the next chained strided descriptor consumed them.
Contiguous extended hides it (single-run generation emits zero bases).

**Fix:** one line in `scheduler.sv` —
`assign w_addrgen_start = w_state_fetch_desc && !r_fetch_desc_d && w_is_ext;`
(gate the generator start on `w_is_ext` so legacy descriptors never touch it).

**Verified:** `test_stream_top_extended_chained_transpose` (was `xfail`, now a
passing regression) + `test_stream_top_extended`; fub scheduler 25/25 and the
datapath macro tests confirm no legacy-path regression.

**Follow-up:** aborted-mid-generation (channel reset) residue in the generator
FIFO is a separate latent robustness item — noted under TASK-058.
