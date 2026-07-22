---
title: BFM usage
summary: Use RDS-DV framework BFMs; never hand-roll. Map + trap list.
---

# Use the framework BFMs - never re-roll

The CocoTBFramework (RTLDesignSherpa-DV repo, editable-installed) plus the
bin/TBClasses wrappers cover every protocol here. Hand-rolled drivers miss
timing corners; hand-rolled decoders desync from packet formats. Missing
BFM = add it to RDS-DV, never inline.

| Interface | Use |
|---|---|
| custom valid/ready | GAXIMaster/GAXISlave (components.gaxi) |
| AXI4 | axi4 factories + AXI4Sequence (never hand-poke s_axi_*) |
| AXI4-Lite / APB / AXIS | axil4 / apb / axis4+axis5 factories |
| MonBus receive | TBClasses.monbus.MonbusSlave |
| MonBus decode | TBClasses.monbus.parse() ONLY |
| MonBus groups | MonbusGroupHarness (scoreboards.monbus_group) |
| Registers | [[registers-by-name]] |

Decision line: standard protocol -> factory; custom valid/ready -> GAXI;
<50-line test-local helper may stay embedded; anything reusable -> RDS-DV.

Traps (each cost real debug time):
- cocotb Monitor.__len__ = queue depth: empty-queue BFM is FALSY, so
  `x.get_stats() if x else {}` silently returns {}. Use `is not None`.
- signal_map requires ALL of {valid, ready, data}.
- Default ready profile delays reach 30 cycles; drain/quiet windows must
  exceed max-delay+refill (~40) AND check bus idle ([[seeds-and-determinism]]
  has the companion rule).
- Don't spawn private _monitor_recv on self-registering components.
- TB classes live in the PROJECT area (projects/**/dv/tbclasses), never in
  the shared framework.
