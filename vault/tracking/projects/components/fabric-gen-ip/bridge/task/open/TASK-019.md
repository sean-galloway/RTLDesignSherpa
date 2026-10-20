# TASK-019: Genesys 2 bridge stress model -- AXI3/AXI5, then AXI-Lite / APB / WB4 shells

**Date:** 2026-10-19
**Priority:** P2
**Status:** OPEN (phase 1, AXI3 and AXI5 sideband/poison done; atomics / IDUNQ / MTE next)
**Owner:** unassigned
**Where:** `projects/fpga-systems/Genesys2/bridge-stress/` (PRD.md), cores in `rtl/amba/shared/axi_stress_*.sv`

## Goal

Silicon validation of the bridge generator on every protocol it builds, with
nothing else on the board: one stress master per DUT master port, one stress
slave per DUT slave port, every byte / ID / response / burst shape checked at
both ends.

## Done (phase 1, 2026-10-19)

- Protocol-neutral cores (master generator + per-ID ordered scoreboard; hash
  slave with reorder / interleave / latency / throttle / SLVERR window), the
  AXI4 shells, regblocks, the generated harness, the Genesys 2 build, the host
  library and board program.
- `val/amba/test_axi_stress_pair.py` (21 cells incl. eight fault injections),
  `dv/tests/test_bs_harness.py` (nine profiles, the board's host code over the
  sim UART), board 27/27.
- Found bridge BUG-018 and converters BUG-010.

## Done (phase 2a, AXI3, 2026-10-19)

- `axi3_{master,slave}_stress`: the generator's LEN_MASK cuts bursts to 16
  beats; the write core carries each beat's WID; the AXI3 slave checks it
  (`ERR_S_WID`). Pair test: AXI4 and AXI3, 42 cells at full level, nine
  faults incl. a flipped WID.
- `bridge_bs_axi3` / `build-axi3` (the CDC ports stay AXI4: no AXI3 CDC in
  the generator), harness generator protocol-aware, board 27/27 and a
  15-minute soak 168/168.
- Found and fixed converters BUG-011 (unaligned chopped INCR).

## Done (phase 2b, AXI5 sideband + poison, 2026-10-19)

- Cores: generic request / response sideband and poison hooks (`SB_MASK`,
  `RSB_MASK`, `POISON`; fixed `SB_M_*` layout in `axi_stress_pkg`). Request
  fields are `f_sb(start address)`; responses echo the request's TRACE
  (`f_rsb`); poison is `f_poison(beat address)`, 1 in 2^n. Nothing is
  stored. Two new codes: `ERR_S_SB`, `ERR_M_SB` (err_mask is now full).
  A slave tells sideband-carrying masters from the rest by the fabric's
  master-index ID field (`SRC_LSB` / `SRC_W`, cfg `sb_src`).
- `axi5_{master,slave}_stress` on the `axi5_*` channel modules (NSAID,
  TRACE, MPAM, MECID, POISON). Pair test: AXI4 / AXI3 / AXI5, 63 cells at
  func, fourteen faults on AXI5 incl. flipped ARTRACE, AWMECID, WPOISON,
  RTRACE, RPOISON, BTRACE.
- `bridge_bs_axi5` / `build-axi5`: a poison clique (cpu -> mem0, mem2), a
  sideband mesh where mem1 takes native (dma), width-converted (io) and
  AXI4 (acc) requests at once, AXI4 CDC ports. Harness generator takes the
  AXI5 pin set and ID layout from the bridge generator itself. Harness sim
  9/9 profiles; board 27/27 and a 15-minute soak 174/174 (~11.1 M bursts);
  WNS +0.066 ns.
- Learned: a trace-capable bridge master port echoes AxTRACE itself
  whatever the slave (bridge BUG-010), and asserts in sim that a
  trace-capable slave echoes it too; the stress slave now does.
- Filed bridge BUG-019 (unaligned INCR steps in several converters).

## Remaining

| Phase | Work |
|---|---|
| 2c | atomics (stateless: an atomic's original data is f_word, so Load/Swap/Compare return it on R; needs an atomic-only ID range shared by the rd and wr cores and R routing to the write core), AxIDUNQ (issue only when the ID has nothing outstanding), MTE (tags as an address hash; BTAGMATCH predicted) |
| 3 | single-beat shells for `axil`/`axil5`, `apb`/`apb5` (slaves in offset mode -- the bridge hands an APB slave a window offset), `wb4`; DUT `bridge_bs_mixed_b.toml` |
| any | re-run `--full-axi` once BUG-018 is fixed and drop the converted-path limits |
