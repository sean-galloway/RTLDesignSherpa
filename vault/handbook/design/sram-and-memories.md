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
- A datapath buffer sized too shallow for concurrent read+write at wide data
  widths corrupts data *silently* - it is not a stall, it is a mismatch. STREAM
  case: a uniform 4 KB buffer meant `fifo_depth=64` at 512-bit, which produced
  data-mismatch errors (the read fill and write drain collided); the fix was to
  scale depth with width and hold a minimum safe depth (128 entries at 512-bit).
  Size buffers by `depth = target_bytes / (data_width/8)` but floor the depth,
  don't floor the byte size.

Authority: /GLOBAL_REQUIREMENTS.md sections 1.2-1.4.
