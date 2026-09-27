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

## An accounting counter must never gate its own count (2026-09-27)

`sram_controller_unit` tracks "beats written minus beats reserved" with
`stream_drain_ctrl`, a virtual FIFO of depth `SD`. Being a FIFO, it has a
`wr_ready`, and its write count is gated on it. But the bound on the REAL
FIFO is set elsewhere -- `stream_alloc_ctrl` allows written minus DRAINED
to reach `SD`, and the latency bridge parks up to five beats outside the
FIFO -- so written minus RESERVED legitimately sits at `SD` while the FIFO
still accepts. The counter then drops a real write: the beat is in the
channel, never reservable, and the source path on rapids ended 4 beats
short of every long transfer (rapids BUG-003, stream BUG-011).

Two rules fall out of it. A counter that exists to OBSERVE a datapath
takes its headroom from the datapath's real bound (here `SD` plus the
bridge), never from its own nominal size; if it is modelled as a FIFO,
size that FIFO past every reachable occupancy and never let its full flag
touch the count. And "isolation passing is not integration passing"
applies at the boundary too: the unit suites (`test_sram_controller*`,
38/38 before and after) cannot reach the trigger, because it needs the
alloc/bridge interplay at exactly `SD` occupancy -- a consumer draining
slower than the fill. The rapids char harness, driving a 512-deep channel
with a 1024-beat transfer at a 50% drain, is what found it; the 84-beat
conservation cells that gated the SRAM swap could not.
