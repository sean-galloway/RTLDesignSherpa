# TASK-001: adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
> **Was `RAPIDS-OBS` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** open 2026-08-05

The beats HAS (`ch06_performance/01_throughput`) already commits to measuring
per-direction bus utilization with the same instrument STREAM uses, and names
wiring it into `rapids_char_harness` as the remaining step. Two things changed
on 2026-08-05 that make that cheaper than it was:

- **`axi4_dma_observer` -> `axi4_intf_master_observer`**, moved to
  `projects/components/misc/rtl/`. The old name was a misnomer (its own header
  said "DMA-agnostic") and read wrong for a block shared by a DMA, a memory
  controller and a characterization harness.
- **It owns its config.** An APB regblock (`obs_regs`, 16 registers) replaced 29
  `cfg_*` ports that each harness had to tie off. Adopting it is now one bridge
  APB slave plus one instantiation, and registers go by name through the
  generated regmap ([[registers-by-name]]).

`dma_slave_monitors` is RETIRED (module and filelist both deleted), and its
`slvmon_regs` regblock was deleted with it on 2026-09-20 as part of STREAM
TASK-073 -- it was superseded, not merely orphaned: BOTH observer roles now
instantiate the shared `obs_regs_top`
(`axi4_intf_master_observer.sv:550`, `axi4_intf_slave_observer.sv:547`).
So the slave-side half of this adoption is `axi4_intf_slave_observer` +
`obs_regs`, not the pair named below. The filelist line quoted here no longer
resolves:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f
    -f $MISC_ROOT/rtl/filelists/dma_slave_monitors.f

**Why it matters:** RAPIDS maps to the observer better than STREAM does -- a
read tap on the source master and a write tap on the sink master give a true
per-direction split, where STREAM's shared master is aggregate-only. And one
instrument across RAPIDS/STREAM/pumice means one definition of a stalled cycle,
so the GB/s numbers in three different reports become comparable.

Related: [[PUMICE-016]] was the same adoption for the memory controller, and
was DROPPED 2026-09-23 — pumice already instantiates the same shared
primitives (`axi_bus_meter`, `axi_perf_latency_hist`) directly, so the
"one definition of a stalled cycle" argument was already satisfied there and
the observer wrapper cost +208% area for nothing. Check whether the same is
true here before adopting: the argument holds only where the meters are NOT
already the shared blocks.
