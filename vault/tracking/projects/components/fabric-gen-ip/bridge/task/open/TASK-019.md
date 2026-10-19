# TASK-019: Genesys 2 bridge stress model -- AXI3/AXI5, then AXI-Lite / APB / WB4 shells

**Date:** 2026-10-19
**Priority:** P2
**Status:** OPEN (phase 1 done)
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

## Remaining

| Phase | Work |
|---|---|
| 2 | `axi3_{master,slave}_stress` (WID, 16-beat, 2-bit lock) and `axi5_*` (the bridge's AXI5 feature groups: atomics, unique, poison/trace/MPAM pass-through); a mixed DUT TOML `bridge_bs_mixed_a.toml` and `build-mixed-a/`; `path_caps` rules for AXI3 (len_mask 15, split) |
| 3 | single-beat shells for `axil`/`axil5`, `apb`/`apb5` (slaves in offset mode -- the bridge hands an APB slave a window offset), `wb4`; DUT `bridge_bs_mixed_b.toml` |
| any | re-run `--full-axi` once BUG-018 is fixed and drop the converted-path limits |
