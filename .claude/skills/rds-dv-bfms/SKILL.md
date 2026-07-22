---
name: rds-dv-bfms
description: Use the RDS-DV framework BFMs (GAXI/AXI4/AXIL/APB/AXIS/MonBus) instead of hand-rolling drivers, monitors, or packet decoders. Covers the factory map, decision tree, and the known traps.
---

# Use the framework BFMs — never re-roll

Every protocol this repo speaks already has a driven, debugged BFM in the
CocoTBFramework (RDS-DV, editable-installed into the venv) with a TBClasses
wrapper layer in `bin/TBClasses/`. Hand-rolling a driver, monitor, or packet
decoder is how timing bugs get missed and how TBs desync from the packet
format. If a BFM seems missing, search first; if genuinely missing, it goes
INTO the framework (RDS-DV repo), not inline into a test.

## What exists (map)

| Interface | Use | Where |
|---|---|---|
| custom valid/ready | GAXIMaster / GAXISlave | CocoTBFramework.components.gaxi |
| AXI4 full | factories + AXI4Sequence, run_axi4_sequence | components.axi4 (never hand-poke s_axi_*) |
| AXI4-Lite | axil4 factories | components.axil4 |
| APB / APB5 | apb factories | components.apb |
| AXI-Stream | create_axis_master/slave/monitor | components.axis4 / axis5 |
| MonBus receive | MonbusSlave | TBClasses.monbus.monbus_slave |
| MonBus decode | parse() ONLY | TBClasses.monbus (never inline bit-twiddling) |
| MonBus groups | MonbusGroupHarness | TBClasses.scoreboards.monbus_group |
| Registers | RegisterMap by NAME | TBClasses.apb.register_map + generated *_regmap.py (no hardcoded offsets) |

## Decision tree

Standard protocol -> its factory. Custom valid/ready -> GAXI. Test-specific
helper under ~50 lines tightly coupled to one test -> may stay embedded.
Anything reusable or >100 lines -> framework (file it against RDS-DV).

## Known traps (each cost real debug time)

- cocotb `Monitor.__len__` = queue depth, so an empty-queue BFM is FALSY:
  `x.get_stats() if x else {}` silently returns `{}`. Use `is not None`.
- `signal_map` now requires ALL of {valid, ready, data} explicitly.
- Default GAXI ready profile delays reach 30 cycles; any drain/quiet window
  must exceed max-delay + refill (~40) AND check the bus idle, or packets
  leak across test-phase boundaries.
- Pin seeds (`RANDOM_SEED`/`COCOTB_RANDOM_SEED`); cocotb self-seeds from the
  clock and results become unreproducible. Corpus + explore pattern:
  val/amba/test_axi_monitor_trans_mgr.py.
- Do not spawn private `_monitor_recv()` on components that self-register
  callbacks; use the public start/ready API.
- TB classes live in the PROJECT area (projects/.../dv/tbclasses), never in
  bin/TBClasses (framework = shared only).

Framework bugs/feature gaps: file in the RDS-DV repo, not here.
