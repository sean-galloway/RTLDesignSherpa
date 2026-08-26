<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

## PUMICE-006 — QoS + advanced scheduling (post-cleanup)
**Status:** active 2026-08-25 — ungated; CSR surface + ALL Axis-2 paging modes
(3/4/5/6/7) landed; next serial axis per Sean's "paging first" = scheduling

**Progress:**
- Step 1 (e64c824b): full mode-select CSR surface + *_STATS telemetry
  registers, defaults bit-identical.
- Axis 2 partial: `pumice_page_policy` fub — modes 1/2 (static ap override),
  3 `fixed_open` (per-bank idle-timeout close via a new lowest-priority
  arbiter PRE branch, JEDEC-gated like the conflict-PRE path) and
  4 `adapt_time` (Happy Intel-adaptive TR/MC walk) + the always-on page
  hit/miss/empty + ACT/PRE/REF counters feeding the *_STATS CSRs.
  Directed test `test_pumice_core_fixed_open` is self-checking both ways
  (mode-0 inertness arms) and mutation-proven (w_timeout_on=0 → RED).
- Axis 2, modes 6/7 `rbl_static`/`rbl_dyn` landed: new `pumice_rbl_table` fub
  (per-set-associative row miss-counter table, tag=row, true-LRU, runtime
  ways/sets shape from PAGE_RBL_CFG, epoch counter clears, mode-7 divider-free
  hill-climb on hit fraction with direction memory). Verdict latched per bank
  at ACT time → page_policy turns the mask into per-bank auto-precharge.
  Directed `test_pumice_core_rbl`: arm A mode-0 thrash baseline, arm B
  thresh=2 static (conflict-PRE suppression < half of baseline + friendly-row
  zero-reACT check), arm C dyn smoke + disarm. Mutation-proven (verdict
  forced 0 → arm B RED: 13 vs 11 PREs, no suppression). Gate tier after:
  fub 40 / macro 3 / top 57.
- Axis 2, mode 5 `adapt_access` landed — AXIS 2 COMPLETE. New
  `pumice_row_pred_table` fub (Happy "Hybrid"): tagless direct-mapped 2-bit
  saturating counters, {bank, XOR-folded row} index; explicit-PRE closes teach
  from accesses-per-activation (<=1 -> close-friendly, >=2 -> open-friendly),
  auto-precharge closes are judged by same-row premature reopen (decrement).
  PAGE_POLICY_CFG.ctr_open_max/ctr_init wired (0 = defaults 2 / weak-open 1;
  init applies while the mode is disabled). LESSON captured in the RTL
  comment: the scheduler's exported row-active bit clears at PICK time, a
  cycle before the PRE issues — the first cut guarded PRE-learning on
  row-active and learned NOTHING (found via $display trace, "PRE bank=4
  act=0"); the open-row IMAGE stays valid, the active bit does not.
  Directed `test_pumice_core_acc` (single-access thrash — a write+read pair
  is 2 accesses and correctly teaches OPEN, so the rbl thrash pattern does
  not transfer): mode-0 baseline, mode-5 suppression < half, golden readback,
  friendly-row zero-reACT, ctr_init=3 cold-table <=1 PRE, disarm. Mutation-
  proven (verdict forced 0 → arm B RED: 12 vs 11 PREs).
  MAS 08_page_policy / design-requirements / HAS open-issue 5 updated to the
  as-built modes 5/6/7.
- Direction (Sean, 2026-08-25): RETIRE the legacy HAPPY_HYBRID predictor —
  the new Happy-derived modes are its successors; docs to describe the
  actual implementation.

Once pumice is CLEAN (board reads validated at the bring-up tuple, refresh
collision fixed + re-soaked on silicon, deskew fully retired, HAS/MAS in sync),
layer in the more sophisticated features planned for the controller: QoS
(per-master/per-ID priority classes into the arbiter pick, ageing/starvation
bounds) and the other advanced-mode work already cataloged in
`projects/components/memory-controllers/ADVANCED_MODES_ROADMAP.md` and the
design-requirements doc (FR-FCFS variants, paging/refresh policy modes).

**Entry gate:** tiny-tREFI soak 0-dirty on the rebuilt bitstream (PUMICE-004).

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

## PUMICE-010 — top-tier shared sim_build races under clean parallel runs
**Status:** open 2026-08-23 — mechanism confirmed twice, serial run is the workaround

`dv/tests/top/test_pumice_top.py::_run` shares one compiled sim per parameter
set (`local_sim_build/shared_nr1` / `shared_nr2`) so the suite compiles ~twice
instead of once per test — but there is NO LOCK around the compile. After
`make clean-all`, `run-gate-parallel` (-n 48) sends dozens of concurrent
Verilator/ccache compiles into the same directory and they destroy each
other's artifacts (`Vtop__pch.h.fast: No such file`, invalid-PCH, missing .o).
Measured 2026-08-23: two consecutive clean parallel runs reported 48 and 31
spurious FAILs (126-144 reruns) on a suite that passes 53/55 serially — the
reruns converge only once one compile survives, so the tally is garbage and
the flake burns ~5 min anyway.

`smoke`/warm-tree parallel runs are fine (nothing to compile). fub/macro use
per-test build dirs and don't race.

**Fix options:** a file lock around the cocotb_test `run()` compile (fcntl on
`<sim_build>/.compile_lock`), or a cheap pre-compile step in the Makefile's
parallel targets (run one test per shared build serially first, then fan out).
Whichever lands, the parallel targets must give an honest tally after
`clean-all` — that is the canonical regression recipe.

Found while validating the RDS-DV#69 fix; the 2 real reds behind the noise are
PUMICE-002 and the LPDDR2 decode regression RDS-DV#70.

**Second finding (2026-08-24): failing seeds are unrecoverable.** One serial
clean tier run showed geared[64/128/256] failing together; the per-test SEED is
`random.randint(0,100000)` at wrapper level, printed nowhere in the summary, and
the logs/ + results xml were wiped by the next `make clean-all` — so the repro
was lost. File-scope reruns and a 10-seed `PUMICE_SEED` sweep (30 runs) all
pass. Whatever fix lands for the lock should ALSO make the wrapper echo each
test's SEED into the pytest summary line (or persist logs/ across clean-all
until explicitly cleared) so a one-off failure is reproducible after the fact.

## PUMICE-011 — multiid read-return accounting: hist total != txn_count (data clean)
**Status:** open 2026-08-25 — deterministic, observability-only

`col_major_bl8_multiid` (id_mode=LFSR) at medium@1000 reports a 1:1 violation:
latency-hist total 168409 vs txn_count 64000 (EXTRA returns) — while the DATA
integrity is clean (0 beats mismatched after the device-wrap fix). The value is
byte-identical across all five controller configs, so it is deterministic and
config-independent → an accounting behaviour of the LFSR-ID x chopped-burst
path, not nondeterministic duplication. Sequencing in `measure()` is clean
(clear_stats after programming, freeze before readback), so it is not
cross-scenario accumulation.

First suspect: `axi_perf_latency_hist` transaction-boundary tracking under
many concurrent IDs — one AXI bl8 burst is 8 chopped BL4 DRAM commands, and
per-ID RLAST collapse may be miscounted when IDs interleave. July's basic-scale
run showed the small-N version (64007 vs 64000). Severity: harness
observability only — the 1:1 check is doing its job of flagging it; data-path
1:1 is separately proven by the CRC/mismatch counters.

Repro: `pumice_master.py --char --char-configs baseline --char-level medium
--char-scale 1000` and watch col_major_bl8_multiid; or in sim,
TEST_CHAR_PROFILE with a multiid scenario over the loopback.
