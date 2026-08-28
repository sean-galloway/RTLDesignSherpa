<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# RAPIDS tasks — open (not started)

### TASK-057: Enforce register-map hygiene in RAPIDS DV (port the STREAM lessons)

**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

**Context:** STREAM had three register-map defects that a coverage/board
bring-up exposed on 2026-07-28/29 (fix: commit `729c774b` + the stream_top_tb
descriptor-fetch proof). RAPIDS is the sibling DMA under `dmas/` and almost
certainly shares the patterns — audit and fix all three:

- [ ] **Use the by-name regmap.** All RAPIDS DV must resolve registers through
  the peakrdl-emitted `rapids_regmap.py` (`RegisterMap` by name), never
  hardcoded APB offsets. STREAM's top TB kicked by hardcoded `0x000 + ch*8` and
  so never touched the regmap — a regmap break passed 8/8 top tests and only
  blew up in the cosims. Mirror the `stream_top_tb` fix (load the regmap in
  setup, resolve `_reg_addr(name)`).

- [ ] **Kick writes MUST look for descriptor reads.** The top/kick tests must
  assert that writing a kick register actually causes a descriptor FETCH —
  observe the descriptor-engine AR channel and prove the kicked descriptor
  address was read — not merely that data moved (a dead/mis-decoded kick path
  still "passes" a datapath-only check if src/dst happen to line up). See
  `stream_top_tb._watch_desc_fetches()` + `assert_descriptors_fetched()`.

- [ ] **No registers done by hand.** Every register must be DEFINED IN THE RDL
  (kick registers as WO, `sw=w; hw=na`, routed to apb4todescr by the cmdrsp
  decode). STREAM had 16 `CHx_CTRL` aliases hand-stuffed into `stream_regmap.py`
  while the RDL declared them "NOT defined here"; a regmap regen dropped them and
  broke every by-name consumer. Verify `rapids_regmap.py` has NO hand-added
  entries — anything a clean `bin/peakrdl_generate.py` run does not emit is a
  latent showstopper. (Regenerate via the bin wrapper only — see
  [[feedback_peakrdl_generate_bin]] equivalent.)

**Done when:** RAPIDS DV resolves every register by name from a regen-clean
`rapids_regmap.py`, the top/kick tests fail if a kick does not fetch a
descriptor, and no register is hand-added.

## RAPIDS-OBS — adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
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

`dma_slave_monitors` moved the same way and on the same terms (own APB
regblock, `slvmon_regs`), since rapids-beats uses the monitored-slave wrapper
too:

    -f $MISC_ROOT/rtl/filelists/axi4_intf_master_observer.f
    -f $MISC_ROOT/rtl/filelists/dma_slave_monitors.f

**Why it matters:** RAPIDS maps to the observer better than STREAM does -- a
read tap on the source master and a write tap on the sink master give a true
per-direction split, where STREAM's shared master is aggregate-only. And one
instrument across RAPIDS/STREAM/pumice means one definition of a stalled cycle,
so the GB/s numbers in three different reports become comparable.

Related: [[PUMICE-016]] is the same adoption for the memory controller.

## RAPIDS-KMAP — RAPIDS-beats has NO contracts workbook at all
**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

Unlike stream and pumice, RAPIDS has **no**
`docs/gen_signal_contracts_kmaps.py` whatsoever. So this is not "finish the
maps" -- it is "there are none". Given RAPIDS-beats was resynced FROM stream
(prefetch, commit-gating, recoverable-timeout all ported across), it inherits
stream's decision shapes without inheriting even stream's partial workbook.

Start by copying the stream generator once [[TOOLING-KMAP]] has promoted the
machinery to `bin/` -- copying it BEFORE that just creates a third private copy
to keep in step.

Targets specific to RAPIDS, in priority order. The first three are OPEN
known_issues, which makes them the highest-value maps in the repo:

1. **Sink data path -- AXI timeout detection missing**
   (`known_issues/active/sink_data_path.md`). A map of the timeout
   qualification cone would make the missing term visible as an axis with no
   contributing expression.
2. **Sink SRAM control -- single-read limitation**
   (`known_issues/active/sink_sram_control.md`). A read-issue qualification map
   with an honest `depends_only_on` is the direct statement of what the
   limitation IS.
3. **`drain_size_gt1` source beat drop**
   (`known_issues/active/drain_size_gt1_source_beat_drop.md`). Beat-drop bugs
   are adjacency bugs; this is the archetypal K-map target.
4. **`scheduler_beats` issue qualification + commit gating.** Ported from
   stream's scheduler, so it carries the same latch/clear and timeout shapes --
   and RAPIDS has no equivalent of stream's macro coverage to catch a
   divergence.
5. **`snk_data_path_axis_beats` credit/RDA accounting.** RAPIDS' network side
   has no counterpart in stream, so nothing stream proved transfers here. This
   is the part of RAPIDS most exposed by having no workbook.
6. **`alloc_ctrl_beats` / `drain_ctrl_beats`.** Same space-accounting shapes as
   stream items 5, but independently drifted since the resync.

Note the naming-conflict history (`known_issues/scheduler_group_signal_naming_
conflicts.md`): RAPIDS has already been bitten by two signals whose names
implied a relationship they did not have. That is the same failure mode the
axis-equation requirement (criterion 3) exists to catch.
