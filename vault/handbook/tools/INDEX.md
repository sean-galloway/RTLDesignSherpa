---
title: Tools
summary: Guides for the repo's own tools and browser apps under bin/ - generators, the svsherpa emitter, the UART harness transport, and the bin/apps calculators.
---

# Tools

Every guide for a tool under `bin/` lives here, not beside the tool
(2026-11-07: see [[doc-placement]] rule 1). A tool's flags stay in its
`--help`.

- [[svsherpa]] - synthesizable SystemVerilog written in Python: a thin emitter, not an elaboration framework
- [[bf16-generators]] - the BF16 arithmetic RTL generators under `bin/rtl_generators/bf16/`
- [[uart-harness-transport]] - `TBClasses.harness`: the shared UART-AXIL transport one host program runs against sim and board; method is [[uart-harness]]
- [[uart-harness-equivalence]] - making the host program identical against sim and board: build order, cocotb.function vs a pump, sticky errors
- [[doc-generation]] and [[signal-contracts-and-kmaps]] live under authoring/ and design/

## Apps (`bin/apps/`)

- [[cache-sim]] - cache associativity simulator; golden parity model for the cache IPs
- [[cdc-drill]] - CDC drill
- [[crc-calc]] - CRC calculator
- [[ddr-drills]] - DDR drills: packs, modes, Pages deploy
- [[ddr-drills-design]] - ddr_drills decision record
- [[ddr-drills-pack-authoring]] - ddr_drills content contract for a new pack
- [[ddr-drills-timing-tables]] - ddr_drills per-pack timing worksheet
- [[fifo-flags]] - FIFO flags calculator
- [[mtbf-calc]] - metastability MTBF calculator
- [[qformat-explorer]] - Q-format explorer
- [[slack-explorer]] - slack explorer
