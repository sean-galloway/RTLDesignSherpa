---
name: rds-dv-bfms
description: Use the RDS-DV framework BFMs (GAXI/AXI4/AXIL/APB/AXIS/MonBus) instead of hand-rolling drivers, monitors, or packet decoders. Covers the factory map, decision tree, and the known traps. The BFM is only ONE of three orthogonal axes - see also rds-dv-axes (sequences) and rds-dv-randomization (timing).
---

# rds-dv-bfms

READ FIRST: vault/handbook/dv/bfm-usage.md (the handbook is the repo's memory; this skill is the
signpost). Never hand-roll a driver/monitor/decoder; the note has the factory map and the trap list (falsy-BFM, signal_map keys, ready-delay windows).

Factories per family: gaxi_factories, axi4_factories, axil4_factories,
apb_factories, axis_factories, fifo_factories. DFI/UART/SMBus have no factory
module - construct components directly. Arbiters: ArbiterMaster +
RoundRobinArbiterMonitor (components.shared); saturate with
force_client_request(), never by poking dut.request - the master owns it.

ONE OF THREE ORTHOGONAL AXES (see rds-dv-axes): BFM = who drives; SEQUENCE =
what traffic (rds-dv-axes); RANDOMIZATION = what timing (rds-dv-randomization).
Using the right BFM says NOTHING about whether the test stresses anything.

Per-family API docs ship in RDS-DV under <RDS-DV>/docs/components/<family>/
(published at sean-galloway.github.io/RTLDesignSherpa-DV). Read them rather
than reverse-engineering from source -- but check what is actually there
first, because coverage is uneven (measured 2026-09-10):

- `components_<family>_interfaces.md` exists for axi4, axi5 and axil4 ONLY.
  This skill used to name that path for every family; for the other eight it
  points at nothing, which sends you to the source it is telling you to avoid.
- A `*_factories.md` page exists for gaxi ONLY, though 11 families ship a
  factories module. The factories arrived after the docs were written.
- Coverage of the rest varies and axil5 has NO pages at all. gaxi and fifo
  are the fullest; apb5, axis5 and wb4 have overview/components/packet;
  `ls <RDS-DV>/docs/components/<family>/` before you rely on any of it.

Gap tracked as an RDS-DV issue; until it closes, the components page plus the
factory docstrings are the honest source for the eight undocumented families.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
