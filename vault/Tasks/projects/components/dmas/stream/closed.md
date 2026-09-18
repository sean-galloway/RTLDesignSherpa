<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — closed (done)

## TASK-081: test_stream_top_basic filed every channel's descriptors under ch0

**Priority:** Medium — a TEST defect, not RTL. It made the engine-vs-descriptor
scoreboard unable to check multi-channel runs, so a real mis-routing bug on any
channel above 0 would have been invisible.
**Status:** [x] Done (2026-09-17) — fixed + regression-tested.

**Symptom:** At `REG_LEVEL=FULL`, `test_stream_top_basic` failed on exactly the
multi-channel cells -- `nc08_dw0512_fd4096_dc04_nch02_apb_config_fast` and
`..._dc08_nch04_apb_config_mixed` -- with
`AssertionError: engine rd/wr cycles do NOT match descriptors`, reporting
`ch0: read beats 384 != descriptor total 768` (and 1088 vs 2176 on the 4-channel
cell). Exactly 2x, only ever `ch0`, deterministic at the same sim time on all
four attempts under `--reruns 3`. Single-channel cells passed.

**Root cause:** `test_stream_top.py:315`, inside `for channel in test_channels:`,
called `tb.write_descriptor(...)` WITHOUT `channel_id`. The parameter defaults to
`0` and flows into `programmed_descriptors.setdefault(channel_id, ...)`, so every
channel's descriptors were filed under `ch0`. The cycle side is attributed
correctly -- `_chan_of()` derives the channel from the AXI ID -- so on iteration 2
the scoreboard compared two channels' descriptors against one channel's beats.
Every other `write_descriptor`/`write_ext_descriptor` call in the file passes
`channel_id=ch`; this one site did not.

**Latent since 2026-07-29** (`e28cf1ab4`, which added the scoreboard). It was
unreachable because the top generator was pinned and multi-channel configs were
never emitted; unpinning it in [[TOOL-016]] (`a33e68181`) generated them for the
first time. NOT an RTL defect and NOT caused by that conversion, whose diff to
this TB is a 9-line `TEST_LEVEL` read touching no accounting code.

**Fix:** one line -- `channel_id=channel,` on the `write_descriptor` call at
`test_stream_top.py:315`.

**Verified:** the two cells pass (250 s, selection guard asserted 2 of 7 so the
`-k` could not pass vacuously), and the scoreboard now scales one channel per
iteration instead of doubling: 68 -> 136 -> 204 -> 272 rd+wr across four
channels. Clean `top` area re-run at FULL after `clean-all`: **52 passed, 3
xfailed, 0 failed** (906 s), zero `do NOT match` in any per-cell log.

## TASK-059: Fix STREAM extended chained strided (transpose) descriptor corruption

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
