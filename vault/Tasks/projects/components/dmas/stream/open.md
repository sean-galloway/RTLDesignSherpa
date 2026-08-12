<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — open (not started)

### TASK-058: Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)

**Priority:** High
**Status:** [~] In progress (2026-07-29) — the canonical workbook already existed
(`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` ->
`stream_signal_contracts.xlsx`); this session brought it CURRENT: added the
`w_addrgen_start` decider K-map (the TASK-059 fix) + `w_is_ext` contract, fixed
the citation drift my scheduler edit caused (24 `CITES` line refs) so
`verify_citations` is green again, and recorded the explicit placement rule in
the canonical note [[signal-contracts-and-kmaps]] (component `docs/`, one per
block, update-in-place — the gap that nearly caused a duplicate). Remaining: the
run-base-generator flush-on-start (invariant **I10** below) and optional formal
SVA of the stated invariants.

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

## STREAM-KMAP — finish the STREAM workbook so its maps prove the decisions
**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` is the
better of the two existing workbooks and still meets only two of the six
criteria in [[signal-contracts-and-kmaps]]: Gray-ordered, computed from cited
RTL -- but no axis equations, no sufficiency argument, no don't-cares, no
implicants. Its first pass found six defects the test suite had not, which is
the argument for FINISHING it, not for calling it done.

It already has per-block builders (`build_rd_engine_kmaps`,
`build_wr_engine_kmaps`, `build_scheduler_kmaps`, `build_desc_engine_kmaps`),
so the work is deepening each rather than starting over.

Priority targets, each with a silicon bug or known_issues entry behind it:

1. **Monitor cfg -> packet-class qualification (`stream_core`). DO THIS FIRST.**
   `cfg_compl_enable` was aliased to `int_cfg_*_mon_enable` and
   `cfg_threshold_enable` to `*_mon_perf_enable`. An axis table carrying each
   axis's DEFINING EXPRESSION would have shown two axes resolving to the same
   signal, immediately. Nothing in the test suite could see it (the FUB tests
   drive the ports directly; the board only sees packets). Small map, live
   failure, and the clearest possible demonstration of criterion 3.
2. **`axi_write_engine` drain strobe / WLAST.** The lost-WLAST deadlock was the
   SRAM drain decoupled from `m_axi_wvalid`; fixed by gating
   `axi_wr_sram_drain` on `m_axi_wvalid && m_axi_wready`. A map of the drain
   strobe with a stated sufficiency argument is the direct check, and
   `wr_w=burst_pause` remains the regression sentinel.
3. **`descriptor_engine` prefetch + fifo_threshold.** `cfg_prefetch_enable` and
   the fifo-threshold input were DEAD -- wired nowhere. A map listing axis
   equations with citations would have shown an axis that no RTL drives.
4. **`scheduler` timeout/error latch and clear.** A sticky CH_ERROR stranding
   the desc_fifo is exactly a latch/clear adjacency question. Note this is the
   SCHEDULER timeout (`SCHED_TIMEOUT_CYCLES`), NOT the monitor timeout -- two
   different mechanisms sharing a word, which is how the monitor's went
   untested at this level for so long.
5. **`stream_alloc_ctrl` / `stream_drain_ctrl` space accounting.** Credit-style
   arithmetic with unreachable regions that are only unreachable because of
   ordering guarantees elsewhere -- those guarantees belong in the don't-care
   citations (criterion 5).

Acceptance: every map above states its axis equations with citations, its
`depends_only_on` argument, its don't-cares with the invariant that makes them
unreachable, and a derived-minimal-vs-RTL verdict.

## STREAM-MONREGS — gate the monitor regfile on a parameter (present + decoded)
**Status:** open 2026-08-06

`stream_regs.rdl` includes and instantiates the monitor regfile unconditionally:

```
line  22:  `include "stream_mon_regs.rdl"
line 758:  stream_mon_regs MON @ 0x1000;
```

There is no parameter deciding whether that block is PRESENT or DECODED, while
`USE_AXI_MONITORS` already decides whether the monitors it configures exist.
The two must move together.

**Why it matters more than area.** On a `USE_AXI_MONITORS=0` build the monitor
registers still accept writes and read back the written value -- driving
nothing. A host arms `RDMON_TIMEOUT`, reads it back correctly, and concludes the
monitor is configured. There is no monitor. Read-back success is normally the
strongest evidence a host has that configuration took, and here it is
affirmatively misleading.

This is live: `build-perf` ships `USE_AXI_MONITORS=0` today, with the whole MON
window responding.

**Wanted:**
- A parameter (`USE_MON_REGS`, defaulting to `USE_AXI_MONITORS`) that gates both
  the regfile instantiation and its address decode.
- With it 0, accesses to 0x1000+ should return the bus error / no-response the
  decode already produces for unmapped space -- so "not built" is
  DISTINGUISHABLE from "built and set to zero". Silence is the honest answer.
- RAPIDS already has the hookup-parameter shape for this
  ([[project_rapids_beats_resync]]: monitors relocated to 0x1000 in a separate
  `include`d regfile under one APB slave with a USE_AXI_MONITORS hookup param).
  Follow it rather than inventing a second pattern.

**Test that should exist alongside it:** the monitors-off build must FAIL to
read the MON window. `dv/tests/top/test_stream_top_mon_cfg.py` covers the
monitors-on direction (register field -> cfg port); the negative direction needs
the parameter first.

Found while writing that test: with monitors ON, the MON window at 0x1000+ needs
`APB_ADDR_WIDTH=13`. At the 12-bit default every monitor register returns
0xDEADBEEF, which is indistinguishable from a hookup failure until you read back
-- see [[STREAM-KMAP]] item 1 for the same class of problem in map form.

---

### TASK-060: Kick STREAM from its own registers — delete the sideband kick ports and apb4todescr

**Priority:** High
**Status:** [ ] Open (2026-08-11)

**Goal:** A channel starts because software wrote a STREAM register, and for no
other reason. Today it starts because the harness pulsed a wire.

**Remove:**

- `i_kick_burst_mask[NUM_CHANNELS]` / `i_kick_burst_addr[NUM_CHANNELS]` — the
  sideband kick pair on `stream_top_ch8` (declared ~line 138-139), plus the
  inline latch/OR-mux that consumes them (`r_kick_burst_pending`,
  ~lines 432-465), and the harness wiring that drives them
  (`harness_csr.o_kick_burst_*` -> `stream_harness` -> stream_top).
- `apb4todescr` — the slow per-channel APB kick route (APB 0x000-0x03F).

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
   (`build-perf` dump.fst, 2026-08-11): `apb_valid_apb4todescr` has exactly one
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

- `grep -rn "i_kick_burst_mask\|apb4todescr" rtl/` returns nothing outside
  history/docs.
- A channel can be kicked with APB/register writes alone, with no sideband
  signal into `stream_top_ch8`.
- Writing 0 to a KICK_ENABLE bit is a no-op; writing 1 kicks once and does not
  re-kick on a subsequent unrelated write.
- Existing 8-channel simultaneous launch still works (one write kicks the
  channels whose bits are set) — that behaviour is wanted, only its plumbing
  changes.
- `test_apb4todescr.py` (fub) retired or repointed at the new FUB.

**Related:** [[project_stream_perf_always_on_meters]]; the kick path was read in
detail while debugging the 8-channel perf hang (TASK-061 territory) — the hang
itself is NOT caused by this and is tracked separately.
