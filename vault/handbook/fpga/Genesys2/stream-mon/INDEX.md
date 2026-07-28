---
title: Genesys 2 / stream-mon
summary: STREAM monitor coverage build + campaign on the Genesys 2 (xc7k325t).
---

# Genesys 2 -- stream-mon

Board- and component-specific docs for the STREAM monitor coverage flow
(`projects/NexysA7/stream_characterization/flows-stream-monitor` ->
`stream_mon_genesys2_top`; `make bitstream` / `make program`). Nested here
rather than flat in the handbook so the vault mirrors the eventual repo layout.

- [[monitor-board-coverage]] - the config-defined dense-tally coverage design
  (per-agent profile tally + UNEXPECTED bin, the roster, the approach)
- [[testplan]] - the 12-32 board sequences that drive that coverage
  (near-concurrent multi-channel, monbus busy-not-flooded)

Host tools: this flow reuses the [[host-tools]] runner suite (DMA, monitor
config, monbus readout) and adds its own `host/poc.py` -- the on-silicon
proof of the primitive routines (link, desc_ram, and the NEW cfg AXIL slave:
profile-CAM load + dense-bin read), run before the testplan sequences.

General FPGA method (build flow, timing, boards, the UART harness) stays in the
flat [FPGA area](../../INDEX.md).
