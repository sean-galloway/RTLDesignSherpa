---
title: SRAMs and memories
summary: No reset ports on SRAMs; ram_style attributes; [DEPTH] syntax.
---

# SRAMs and memories

- SRAM modules have NO reset port. Controllers own pointers and reset;
  memory contents are init-by-write. Shared primitives:
  `rtl/amba/gaxi/gaxi_fifo_sync.sv`, `rtl/amba/shared/sdpram_core.sv`
  (+ the sdpram_slave_* protocol wrappers). The old simple_sram.sv is gone.
- FPGA inference attributes on every memory array:
  `(* ram_style = "auto"|"distributed"|"block" *)` (Xilinx) with the Intel
  comment variant beside it. Small FIFOs: distributed.
- Array syntax `[DEPTH]`, never `[0:DEPTH-1]`.
- FIFO depths: power of 2 ([[cdc]] for why async cares even more).

Authority: /GLOBAL_REQUIREMENTS.md sections 1.2-1.4.
