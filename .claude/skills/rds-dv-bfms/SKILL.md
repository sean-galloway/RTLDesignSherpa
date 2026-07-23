---
name: rds-dv-bfms
description: Use the RDS-DV framework BFMs (GAXI/AXI4/AXIL/APB/AXIS/MonBus) instead of hand-rolling drivers, monitors, or packet decoders. Covers the factory map, decision tree, and the known traps. The BFM is only ONE of three orthogonal axes - see also rds-dv-axes (sequences) and rds-dv-randomization (timing).
---

# rds-dv-bfms

READ FIRST: docs/handbook/dv/bfm-usage.md (the handbook is the repo's memory; this skill is the
signpost). Never hand-roll a driver/monitor/decoder; the note has the factory map and the trap list (falsy-BFM, signal_map keys, ready-delay windows).

Factories per family: gaxi_factories, axi4_factories, axil4_factories,
apb_factories, axis_factories, fifo_factories. DFI/UART/SMBus have no factory
module - construct components directly. Arbiters: ArbiterMaster +
RoundRobinArbiterMonitor (components.shared); saturate with
force_client_request(), never by poking dut.request - the master owns it.

ONE OF THREE ORTHOGONAL AXES (see rds-dv-axes): BFM = who drives; SEQUENCE =
what traffic (rds-dv-axes); RANDOMIZATION = what timing (rds-dv-randomization).
Using the right BFM says NOTHING about whether the test stresses anything.

Authoritative per-family API docs ship in RDS-DV:
<RDS-DV>/docs/components/<family>/components_<family>_interfaces.md
(published at sean-galloway.github.io/RTLDesignSherpa-DV). Read those rather
than reverse-engineering from source.

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
