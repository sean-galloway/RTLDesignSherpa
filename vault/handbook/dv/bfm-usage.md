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

| Arbiters | ArbiterMaster + RoundRobinArbiterMonitor (components.shared) |

Decision line: standard protocol -> factory; custom valid/ready -> GAXI;
<50-line test-local helper may stay embedded; anything reusable -> RDS-DV.

Factory entry points, per family (count = callables in that file):
`gaxi_factories` 8, `axi4_factories` 17, `axil4_factories` 18,
`apb_factories` 7, `axis_factories` 11, `fifo_factories` 14. DFI, UART and
SMBus have no factory module - construct their components directly
(`dfi_master_mc.py`, `uart_components.py`, `smbus_components.py`).

This note covers the BFM axis ONLY. What traffic to send (sequences) and what
timing shape to send it at (randomization) are INDEPENDENT choices - see
[[rds-dv-axes]] for the three-axis framing, and [[randomization]] for the
profile catalogue. Using the right BFM says nothing about whether the test
stresses anything.

Authoritative per-family API docs live in RDS-DV itself
(`docs/components/<family>/`, published at
sean-galloway.github.io/RTLDesignSherpa-DV) - read those rather than
reverse-engineering from source.

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
