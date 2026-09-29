# TASK-010: Kick STREAM from its own registers — delete the sideband kick ports and the APB kick block
> **Was `TASK-060` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

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
