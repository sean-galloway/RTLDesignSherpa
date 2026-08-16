<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

## PUMICE-002 — test_pumice_top_csr wr_rd roundtrip returns zero read beats
**Status:** open 2026-07-23 — pre-existing, re-confirmed twice by bisection

`cocotb_test_pumice_top_csr` fails its AXI write-then-read phase: read 0 gets
ZERO R beats in 800 cycles (`got=[]`), i.e. the read path never returns — while
`test_pumice_top` (45 read-heavy tests), core, core_dfi, geared and the whole
fub/macro suite pass.

**Bisected 2026-07-21:** fails identically at HEAD (95c9490a) with only the
filelist fix applied — predates the deskew removal and the refresh/tRFC arbiter
change.

**Re-confirmed 2026-07-23:** fails identically with `pumice_top.sv` reverted to
HEAD and a clean rebuild, so it is not caused by the PUMICE-001 page_policy fix
either. Note the rebuild mattered — the first run reused a stale `sim_build`
and completed in 0.41 s, which would have made a reverted-RTL run meaningless.

Suspect the CSR-programmed config path (hwif-driven init) diverging from the
TB-driven config the other tops use. The top tests were compile-broken (missing
`gaxi_fifo_async` deps in the dv/tb filelists) for some window, so the
regression that introduced this was masked.

## PUMICE-003 — test_ddr2_char_char_families integrity fail (bank_interleave/incremental_bl8)
**Status:** open 2026-07-23 — pre-existing, same class as PUMICE-001

`bank_interleave/incremental_bl8` fails integrity in the char-families sim
("read engine did not complete", 42 beats mismatched).

**Bisected 2026-07-22:** fails identically at HEAD (95c9490a) — predates the
deskew removal, the refresh/tRFC arbiter change, and the no-rmw shadow writes.
Same masked-regression window as PUMICE-002 (the top/char sims were
compile-broken by the dv/tb filelist drift for a period).

Suspect the config-switch path (ADDR_MAP `bank_lsb=0` preset) interacting with
the read engine. Re-check whether the PUMICE-001 fixes move this before
debugging further.

## PUMICE-004 — Refresh collides with an open row (arbiter registered-feedback hazard)
**Status:** open 2026-07-23 — confirmed on silicon; instrument wired, fix not started

**Bug (#2, command-sequencing).** The arbiter (`pumice_cmd_arbiter`) can grant a
`REFab` immediately after an `ACT` to the same bank WITHOUT a `PRE` in between —
refreshing a row that is still open — and the following `RD` then returns
garbage (zero) for that one read.

Root: the per-bank "safe signals" (`pumice_bank_timers` readiness) are COARSE
and REGISTERED (2-cycle event->ready latency, see the `r_guard` note in the
arbiter), so the combinational picker issues the `ACT`, and the refresh path's
precharge-before-REF check does not yet see the just-opened row -> REF fires
with the row open.

**Reproduced pre-silicon** in `engine_mirror[64]` (`test_pumice_top`),
gear-2/BL8, sustained b2b: burst 25 shows `ACT@31920000 -> REF@31940000 (no PRE)
-> RD@31980000` -> read returns `0x0` (golden `0x190000`); refresh cadence
~10.25 us lands on one read. On the BOARD (gear-4, ILA
`reports/ila_refresh_collide.csv`) the refresh is correctly sequenced
(`RD->PRE->REF->ACT->RD`) — so this is not the board blocker, but it IS a real
arbiter defect. Confirmed on silicon as the residual row-sized corruption in
PUMICE-005.

**Instrument (already wired):** `rtl/fub/pumice_cmd_history_checker.sv`
(generate-gated by `CMD_HISTORY_EN` inside `rtl/macro/pumice_mem_cmd_scheduler.sv`)
— a per-(rank,bank) command-history shift register (slot = cycles-since-issue)
that binds to the arbiter's `cmd_valid/op/rank/bank` and audits JEDEC same-bank
sequencing the coarse gate misses. Ships the refresh-collision assertion (no
`REFab` with any bank row open) plus optional tRCD/tRP/tRAS positional checks.
Coarse = *permission to issue* (forward, lossy); fine = *record of what issued*
(backward, exact) — you need the fine one to audit the coarse one.

**Plan:**
1. `bind` the checker in the arbiter FUB (`test_pumice_cmd_arbiter`) and/or the
   scheduler MACRO (`test_pumice_core_macro`) TBs; add `--assert` to the
   verilator compile args.
2. Reproduce as a directed pre-silicon test — small `tREFI` + sustained
   same-bank reads -> the checker fires RED. **The test MUST also do DATA
   checking** (golden read compare), not just the sequencing assertion.
3. Fix the arbiter refresh sequencing: the precharge-before-REF logic must
   account for a just-issued `ACT` (don't grant `REF`/`REFab` while any bank's
   most-recent row-affecting op is an `ACT`), or block the `ACT` when a refresh
   is being sequenced. Mirror the fix in `refresh_ctrl`/`pumice_cmd_arbiter`.
4. Re-verify: checker GREEN, `engine_mirror[64]` burst-25 read == golden, macro
   109 + gear2 + FUB stay green.
5. Rebuild the bitstream (also picks up the APB CDC fix) and re-soak at tiny
   tREFI as the regression gate.

Scope note: this checker catches command-SEQUENCING bugs only.

## PUMICE-006 — QoS + advanced scheduling (post-cleanup)
**Status:** open 2026-07-23 — gated, do not start yet

Once pumice is CLEAN (board reads validated at the bring-up tuple, refresh
collision fixed + re-soaked on silicon, deskew fully retired, HAS/MAS in sync),
layer in the more sophisticated features planned for the controller: QoS
(per-master/per-ID priority classes into the arbiter pick, ageing/starvation
bounds) and the other advanced-mode work already cataloged in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md` and the
design-requirements doc (FR-FCFS variants, paging/refresh policy modes).

**Entry gate:** tiny-tREFI soak 0-dirty on the rebuilt bitstream (PUMICE-004).

## PUMICE-007 — Retire the deskew RTL + PHY_TIMING.deskew_lo/hi CSR
**Status:** open 2026-07-23 — removal candidate, issue #39

The deskew path was superseded (see PUMICE-008 in `dropped.md`): the board read
fix was the PUMICE-005 bring-up tuple at deskew 0/0. The RTL and its CSR fields
remain and cost area/timing. Delete rather than train — but only after the
board is re-validated on a rebuilt bitstream so the removal is not entangled
with an active bring-up.

---

## PUMICE-008 — adopt axi4_intf_master_observer (APB-configured) for perf observation
**Status:** open 2026-08-04

pumice rolls its own perf observation: `perf_rd_prod/bp/starv/idle`,
`perf_rd_hist_count/total`, `perf_clear`, `perf_freeze` wired out of the harness
and read back through harness CSRs. The stream flows use
`axi4_intf_master_observer`, an inline pass-through meter over the same primitives
(`axi_bus_meter`, `axi_perf_latency_hist`) that also emits monbus packets.

**What changed that makes this worth doing (2026-08-04):** the observer now
carries its OWN APB config regblock (`obs_regs`) instead of exporting 29 `cfg_*`
ports for the instantiating harness to tie off, and it moved to
`projects/components/misc/rtl/` so it is reachable from any board flow:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f

So adopting it costs one bridge APB slave and one instantiation, not 29 tie-offs
and a harness that has to know the block's internals. Registers are by name via
the generated regmap (see [[registers-by-name]]).

**Why bother:** pumice and stream currently measure throughput with different
code, so their numbers are not strictly comparable — which matters because the
pumice-vs-LiteDRAM A/B and the stream characterization both report MB/s. One
meter means one definition of a stalled cycle, and pumice would inherit the
latency histogram and the monbus packet path for free.

**Scope note:** the observer is an AXI4 pass-through meter (it was called
`axi4_dma_observer` until 2026-08-04; the DMA in the name was always wrong). pumice's interesting
traffic is on the DFI side, so this covers the AXI front-end (host -> pumice_top)
rather than DRAM-side behaviour; the DFI meters stay as they are.

**Not urgent.** Do it when the pumice harness is next opened for other reasons,
not as a standalone change — it touches the bridge map and the harness CSR
readback, and pumice bitstreams are on the critical path for the DDR2 work.

## PUMICE-CLEANUP — doc + filelist cleanup (push from workstation)
**Status:** open 2026-07-24 — deferred (project cleanup; see TOOL-010)
**Priority:** P2

Apply the RTL-area cleanup pattern to pumice: doc placement ([[doc-placement]])
and filelist consistency ([[filelists]] — the `dv/tb/*_tb_top.f` move into a
`filelists/` dir co-located with the testbench).

**⚠️ Pushing: Sean pushes pumice from the workstation, NOT from the agent
environment (Sean, 2026-07-24).** Make and commit the pumice changes here if
working, but leave the push to Sean. Do not `git push` pumice work from this
box. (Reason per Sean — workstation is where pumice is pushed from.)

Gated behind the RTL area completing (Tasks/INDEX.md sequencing).

## PUMICE-KMAP — real K-maps for the scheduler, CAMs and DFI layer
**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

`pumice-ddr2-lpddr2/docs/gen_signal_contracts_kmaps.py` emits maps that meet two
of the six criteria in [[signal-contracts-and-kmaps]]: no axis equations, no
sufficiency argument, no don't-cares, no implicants. Its `axis|axes|index`
mention count is 1.

Map these, because each is combinational, safety-relevant, and has already
produced silicon bugs:

- **`pumice_mem_cmd_scheduler` arbitration/issue qualification.** Two
  double-issue hazards were caught only by the MACRO test, from registered
  feedback latency -- exactly what a map with an honest sufficiency argument
  would have surfaced ([[pumice-mem-cmd-scheduler]]).
- **Bank timers / open-page decision.** Runtime page policy shipped an 8.8x
  streaming win; the decision cone deserves a proof, not a picture.
- **`wr_data_cam` fill/drain and the `agg||last` B-gating.** The fill/drain race
  (fixed by `r_fdone`) is precisely a two-sided adjacency question.
- **DFI command/phase placement.** The rd_phase and write-latency confusion cost
  weeks on the board; a map with cited axes would have made the phase
  assumptions explicit instead of implicit.

Each map must name the invariant that makes its unreachable cells unreachable --
several of the above have "cannot happen" regions that are true only because of
ordering guarantees elsewhere, and those guarantees belong in the citation.
