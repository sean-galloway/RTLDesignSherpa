---
title: Nexys A7 / stream-char
summary: STREAM characterization (bridge) flow on the Nexys A7 + its host tools.
---

# Nexys A7 -- stream-char

Board- and component-specific docs for the STREAM characterization flow
(`projects/NexysA7/stream_characterization/flows-stream-bridge` ->
`stream_char_top`). Nested here rather than flat in the handbook so the vault
mirrors the eventual repo layout.

- [[host-tools]] - the flows-stream-bridge/host runner suite (DMA, monitor
  config, monbus/trace readout, perf) that drives sim and silicon identically

General FPGA method (build flow, timing, boards, the UART harness pattern) stays
in the flat [FPGA area](../../INDEX.md); the Genesys 2 monitor-coverage build
that reuses these tools is [Genesys2/stream-mon/](../../Genesys2/stream-mon/INDEX.md).
