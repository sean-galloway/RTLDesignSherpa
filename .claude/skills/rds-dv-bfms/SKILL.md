---
name: rds-dv-bfms
description: Use the RDS-DV framework BFMs (GAXI/AXI4/AXIL/APB/AXIS/MonBus) instead of hand-rolling drivers, monitors, or packet decoders. Covers the factory map, decision tree, and the known traps.
---

# rds-dv-bfms

READ FIRST: docs/handbook/dv/bfm-usage.md (the handbook is the repo's memory; this skill is the
signpost). Never hand-roll a driver/monitor/decoder; the note has the factory map and the trap list (falsy-BFM, signal_map keys, ready-delay windows).

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
