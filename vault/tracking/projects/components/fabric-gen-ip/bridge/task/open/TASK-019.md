# TASK-019: Genesys 2 bridge stress model -- AXI3/AXI5, then AXI-Lite / APB / WB4 shells

**Date:** 2026-10-19
**Priority:** P2
**Status:** OPEN (phase 1 and AXI3 done)
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

## Remaining

| Phase | Work |
|---|---|
| 2b | `axi5_*` (the bridge's AXI5 feature groups: atomics, unique, poison/trace/MPAM pass-through); a mixed DUT TOML and build |
| 3 | single-beat shells for `axil`/`axil5`, `apb`/`apb5` (slaves in offset mode -- the bridge hands an APB slave a window offset), `wb4`; DUT `bridge_bs_mixed_b.toml` |
| any | re-run `--full-axi` once BUG-018 is fixed and drop the converted-path limits |
