<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — closed (done)

## TASK-058: Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)

**Priority:** High
**Status:** [x] Done (2026-09-20) — closed by Sean. The optional formal
SVA of the stated invariants was NOT done; everything else the task asked
for is landed (036efde88). Original in-progress record follows.
**Was:** [~] In progress (2026-07-29) — the canonical workbook already existed
(`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` ->
`stream_signal_contracts.xlsx`); this session brought it CURRENT: added the
`w_addrgen_start` decider K-map (the TASK-059 fix) + `w_is_ext` contract, fixed
the citation drift my scheduler edit caused (24 `CITES` line refs) so
`verify_citations` is green again, and recorded the explicit placement rule in
the canonical note [[signal-contracts-and-kmaps]] (component `docs/`, one per
block, update-in-place — the gap that nearly caused a duplicate). Remaining: the
run-base-generator flush-on-start (invariant **I10** below) and optional formal
SVA of the stated invariants.

**Update 2026-09-20.** The citation gate was RED again (21 drifts, not caused by
this area's edits -- `scheduler.sv` moved +3 in `db672cd03`, `stream_core.sv`
+26 in `4aeaf3e63`, the monitor files up to +195 in `657d413c1`). Restored to
green; `CITES` is 73 -> 83. Four findings came out of doing it:

1. **The saturation-recovery contract documented the DEFECT as the contract.**
   Every row was stale: `cmd_entry_reserve` 2 -> **4**, `BLOCK_MARGIN` 1 -> **3**,
   `MAX_TRANSACTIONS` `+4`/68 -> `+MON_TRANS_MARGIN`/**72**, thresholds 67 -> 69.
   `axi_monitor_base.sv:679-690` states plainly that reserve=2 (margin 1) is the
   mechanism behind the observer tracking loss (4096 observed vs 3073 tracked) --
   so the workbook was publishing the broken sizing as correct. Corrected.
2. **`stream_core.sv` carried the same stale arithmetic** in comments ("+4
   covers in-flight skid/handshake overlap", "8ch default = 68"), orphaned by
   `baac9a77a` when MON_TRANS_MARGIN became 8. Corrected (comment-only;
   `stream_top_ch8` re-elaborates clean).
3. **"invariant I10" is a dangling reference.** There is no I-numbering anywhere
   in the generator -- invariants are free text in the "Key invariant" column.
   The numbered list the status line above promises was never written. Rather
   than invent an I10 to match the prose, the invariant is now recorded in the
   required form and numbered locally (I1-I3).
4. **86 source labels are structurally uncheckable.** `verify_citations` only
   validates `CITES` quoted snippets; the `f"{SCHED}:924-940"`-style labels are
   line RANGES, so drift in them is undetectable by design. Confirmed real, not
   theoretical: `SCHED:924-940` labels the read-prefetch map, but line 924 is now
   a comment and the expression sits at 927. Not fixed here -- making ranges
   checkable is tooling work ([[TOOLING-KMAP]] step 5), which [[STREAM-KMAP]] is
   already blocked on.

**Run-base generator: documented, deliberately NOT fixed in RTL.** The hazard is
confirmed and now bounded rather than vague: `u_rd_addr_gen`/`u_wr_addr_gen` take
`.rst_n(rst_n)` (SCHED:1029, :1051) -- the BLOCK reset -- so `r_channel_reset_active`
never reaches them (I1); `start` re-arms only the walker and never clears
`i_addr_fifo` (ADDRGEN:152) (I2); depth is 4 per direction (I3). So a channel
reset mid-generation strands up to **4 stale bases per direction**, and the next
descriptor generates behind them. Landed as a three-part CONTRACT TABLE (terms ->
invariants -> decision table) on the "K-maps scheduler" sheet. The decision table
has NO illegal row: all eight combinations are reachable, so nothing structurally
prevents the case -- it is bounded, not excluded.

RTL was left alone on purpose. The task's own text calls this "a good candidate
for the signal-contract treatment", the earlier `gaxi_drop_fifo_sync` `drop_all`
attempt regressed working cases and was reverted, and that attempt exists in no
branch, reflog or stash -- so it cannot be inspected and re-attempting it blind
would just reproduce the regression. Recorded hypothesis for whoever picks it up:
`gaxi_drop_fifo_sync` blocks normal read/write for the duration of a drop, which
is the likely "flush/read-timing interaction". Note the block is shared with
RAPIDS since `4aeaf3e63`, so an RTL flush has two consumers.

Also worth knowing: **no table in the workbook used the 2026-08-28 required form
until this one.** The handbook calls term-list -> invariants -> decision-table the
governing requirement; the existing sheets are all the older shape. Converting
them is [[STREAM-KMAP]] scope.

**Remaining:** only the explicitly-optional formal SVA of the stated invariants.
Everything the status line above listed as outstanding is now either done or
consciously deferred with a reason, so High priority may no longer be right.

**Goal:** Maintain explicit **signal contracts** and **Karnaugh maps** for the
significant control/handshake signals in STREAM — **especially in the read and
write engines** (`axi_read_engine.sv`, `axi_write_engine.sv`) and the scheduler /
descriptor-engine / SRAM-controller handshakes — so the design is provably
correct **by construction** rather than only by directed test.

**Why:** STREAM has already produced several *interaction* bugs that a per-signal
contract would have forbidden up front, not caught after the fact — the
WLAST/drain lost-beat deadlock, the SRAM drain double-count deadlock, and now
the extended chained-transpose corruption (TASK-059 / known_issues). Each was a
cross-block pipeline hazard: a signal asserted (or sampled) one cycle off, or a
shared config register aliased across descriptors. A written contract per signal
(producer, consumer, valid window, mutual-exclusion / one-hot invariants,
back-to-back and reset behaviour) plus a K-map for the combinational deciders
turns these into things that are wrong *on paper* before they ship.

**Scope (significant signals — at least):**
- Engine handshakes: `m_axi_*valid/ready`, `*last`, the SRAM `drain`/`valid`
  pair, per-channel `grant`/`req`, `w_active`/registered-valid gating.
- Scheduler FSM enters/exits and the write-completion timeout.
- Descriptor-engine prefetch + extended `chunk1` fetch (`w_want_ext`,
  `g_ext_fifo`) and the `stream_run_addr_gen` config-latch enables.
- Address generation stride/index/wrap deciders (K-map the mode selection:
  burst vs per-beat, wrap on/off).

**Deliverable:** a contract note per significant signal (table: producer /
consumers / valid window / invariants / reset) and K-maps for the combinational
deciders, landed under the STREAM docs tree (HAS/MAS or a dedicated
`signal_contracts/` area) and indexed. Cross-link each contract to the RTL line
and to any known_issue it would have prevented.

**Related follow-up (from TASK-059's fix):** the run-base generator
(`stream_run_addr_gen`) can still retain queued bases if an extended descriptor
is aborted mid-generation by channel reset (channel reset does not reach that
block). A flush-on-start (`gaxi_drop_fifo_sync` `drop_all`) would close it; a
first attempt regressed the working cases on a flush/read-timing interaction and
was reverted. Low-severity latent robustness item — a good candidate for the
signal-contract treatment.

---

## TASK-060: Kick STREAM from its own registers — delete the sideband kick ports and the APB kick block

**Priority:** High
**Status:** [x] Done (2026-09-18) — both halves verified complete.
The sideband `i_kick_burst_*` ports were already gone (zero hits in any
`.sv`/`.svh`); the APB kick block was deleted in 640670341 together with its
filelist, TB, test, testplan, GTKW, formal block, the `stream_all.f` include
and the `formal/stream/Makefile` MODULES entry. Verified not instantiated
anywhere before deleting, and both `stream_top_ch8` and `rapids_beats_top`
elaborate clean afterwards.

**Goal:** A channel starts because software wrote a STREAM register, and for no
other reason. Today it starts because the harness pulsed a wire.

**Remove:**

- `i_kick_burst_mask[NUM_CHANNELS]` / `i_kick_burst_addr[NUM_CHANNELS]` — the
  sideband kick pair on `stream_top_ch8` (declared ~line 138-139), plus the
  inline latch/OR-mux that consumes them (`r_kick_burst_pending`,
  ~lines 432-465), and the harness wiring that drives them
  (`harness_csr.o_kick_burst_*` -> `stream_harness` -> stream_top).
- the APB kick block — the slow per-channel kick route (APB 0x000-0x03F).

**Replace with:** a new FUB that owns the descriptor-address handoff:

- takes the **64-bit** descriptor address per channel from **cfg registers**
  (not a sideband bus, not a 32-bit shadow);
- drives the descriptor engine's valid/ready handshake, holding valid until
  accepted so no kick is lost when a channel is briefly unready;
- fires a channel **only** when a **write-only KICK_ENABLE** register has a 1
  written to that channel's bit — write-1-to-kick, self-clearing, no readback
  state to get stale.

**Why (three things this fixes):**

1. **STREAM's start condition is currently invisible in its own register map.**
   `stream_top_ch8` has zero `cfg_*` input ports — config is properly internal —
   but the kick is punched in from outside on a wire. Nothing in STREAM's
   registers or APB traffic records that a transfer began.
2. **Two kick paths, one dead.** MEASURED in the 8ch perf sim
   (`build-perf` dump.fst, 2026-08-11): the kick block's `apb_valid` has exactly one
   value-change in the whole run (its reset) and never asserts; every kick came
   via `r_kick_burst_pending`. Two routes into the same port, one of them dead
   code in every real flow, and the dead one carries the obvious names — so a
   trace reader looking for `apb_descriptor_kickoff_hit` / `cmd_to_kickoff`
   concludes the descriptor engines started themselves. That cost real debug
   time on 2026-08-11.
3. **The address map has a live foot-gun.** `KICK_GO` sits at 0xC0, in the
   MIDDLE of the per-channel kick-address slots (ch0-3 at 0xB0-0xBC, ch4-7 from
   0xC4). A naive `base + ch*stride` walk lands ch4 on 0xC0 and writes a
   descriptor ADDRESS into `KICK_GO`, firing a spurious kick with a garbage
   mask. `bin/harness_kick.py` documents this and resolves slots by name to
   dodge it — but the layout should not need dodging.

**Also fixes a width truncation:** the current shadow path is 32-bit
(`harness_csr.r_kick_addr[31:0]`) while STREAM's descriptor addresses are
64-bit. The new registers carry the full 64 bits.

**Acceptance:**

- `grep -rn "i_kick_burst_mask" rtl/` returns nothing, and the kick block is
  deleted repo-wide (verified 2026-09-18).
- A channel can be kicked with APB/register writes alone, with no sideband
  signal into `stream_top_ch8`.
- Writing 0 to a KICK_ENABLE bit is a no-op; writing 1 kicks once and does not
  re-kick on a subsequent unrelated write.
- Existing 8-channel simultaneous launch still works (one write kicks the
  channels whose bits are set) — that behaviour is wanted, only its plumbing
  changes.
- the fub kick-block test retired (deleted in 640670341).

**Related:** [[project_stream_perf_always_on_meters]]; the kick path was read in
detail while debugging the 8-channel perf hang (TASK-061 territory) — the hang
itself is NOT caused by this and is tracked separately.


---

## Configurable decompression in `monbus_tally_axil` (LOW priority, future)

**Priority:** low. Nothing is blocked on it — the compression format is already
verifiable without it (see "not blocked" below).

**What:** let the tally ingest the COMPRESSED monbus stream, not just RAW
3-beat records, selected at runtime.

**Why it does not exist today:** the tally reconstructs each 128-bit packet with
a mod-3 counter over the ingest write stream:

```
beat0 = {tag[3:0]=0, source_ts[59:0]}
beat1 = packet[127:64]
beat2 = packet[63:0]
```

That layout only holds for `USE_COMPRESSION == 0`. With compression on, the
beats are Tier-0/Tier-1 slots and the mod-3 reassembly produces garbage — which
is why `OBS_CTRL.COMPRESS_EN` carries the warning "leave 0 unless the consumer
decompresses". The tally is that consumer, and it cannot.

**What the decoder has to do** (README_COMPRESSION_DATASET.md 2.5, "Decoder
mirror"): reconstruct CAM state from the slot stream alone, with no
out-of-band information. Tier-0 escapes install templates; Tier-1 hits
reconstruct `(key, event_data)` from `CAM[idx]` plus the slot fields, and must
touch the CAM in exactly the same order the encoder did. So this is a stateful
CAM-maintaining decoder, not a beat reshuffle — the real work of the task.

**Not blocked on this** — deliberately. `comp_sram` (sdpram_slave_axil_axil,
`0x001A0000`, 64 KB) was added to the bridge so compressed traffic can be
written to an ORDINARY memory and read back by the host, then compared against
the bit-exact Python golden `bin/TBClasses/monbus/monbus_compressor.py`. That
verifies the format on silicon without any RTL decoder. The tally decoder is a
convenience (decode in hardware, tally directly) rather than a prerequisite.

**Acceptance:**

- A runtime bit selects RAW vs COMPRESSED ingest; RAW behaviour is bit-identical
  to today when it is clear.
- Decoding the dataset in `reports/compression_dataset/` reproduces the original
  records bit-exactly, matching the Python decoder (682 records, 32 templates,
  93.5% Tier-1 hit rate is the published bring-up target).
- A compressed run and a raw run of the same traffic produce the SAME tally bins.

**Related:** [[project_stream_mon_tally_coverage]]. Format spec + dataset:
`projects/NexysA7/stream_characterization/reports/compression_dataset/README_COMPRESSION_DATASET.md`.

---

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
