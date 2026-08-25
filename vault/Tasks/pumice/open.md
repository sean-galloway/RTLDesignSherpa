<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Open (accepted, not started)

---

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
