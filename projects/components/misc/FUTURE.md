# Miscellaneous Components - Future Work

Tracker for planned integrations of the modules in this directory. Plain
Markdown (working tracker, not a house-style deliverable doc).

---

## FUTURE-001: Integrate `dma_address_gen.sv` into the STREAM scheduler

**Status:** Idea / thought experiment (scoped, not started)
**Priority:** P3 (opt-in, post-v1.0 enhancement — NOT a base-STREAM fix)
**Module:** `projects/components/misc/rtl/dma_address_gen.sv`
**Consumer:** `projects/components/stream/rtl/fub/scheduler.sv`

### Idea

STREAM's `scheduler.sv` currently accumulates read/write addresses linearly
each burst (`r_src_addr <= r_src_addr + (beats_done << clog2(DATA_WIDTH/8))`).
Add two `dma_address_gen` instances (one read, one write), each configured from
the descriptor, to turn STREAM from contiguous-only into a strided / 2D-tiled /
circular / reverse / scatter-transpose DMA — the scatter-gather the name implies
— while keeping linear as the default (existing descriptors and tests unchanged).

STREAM's present linear mode is the strict subset `stride_0 = beat_size,
stride_1 = 0, wrap = 0`, so the change is additive and backward compatible.

Shape (see TASK-101 for the full spec):

- **Gated by compile-time `USE_ROW_COL_MAJOR_ADDRESSING`.** `0` = scheduler AND
  descriptor_engine unchanged, 256-bit descriptors only. `1` = two
  `dma_address_gen` FUBs drive addressing, both descriptor formats accepted.
  Design intent: the gate is **surgical/localized**, not `if (param)` sprinkled
  through every module.
- **Two generators + queues.** `u_rd_addr_gen` (src) and `u_wr_addr_gen` (dst),
  each feeding an address FIFO so addresses are produced run-ahead of
  consumption (hides the 2-stage latency). Independent rd/wr iteration is what
  enables **transpose** (row-major read <-> col-major write). The address FIFOs
  are decoupled from the param — usable in legacy mode too, required for new-mode
  timing, and carrying their own supporting design updates.
- **Variable-length descriptors.** A `desc_type` field in the first 256-bit chunk
  selects 256-bit legacy (1 chunk, linear) vs 512-bit extended (2 chunks,
  addr-gen). `descriptor_engine` conditionally fetches the second half; the
  scheduler dequeues one or two chunks accordingly. Mixed chains supported;
  `desc_type=0` is bit-for-bit today's behavior.

### Why it's low-risk RTL / high-cost plumbing

- `dma_address_gen` is a proven module (`result_addr = base + index_0*stride_0
  + index_1*stride_1`, signed strides + power-of-2 wrap masks, 2-stage
  pipelined, valid/ready). It is already driven this exact way in
  `rtl/amba/shared/axi4_master_wr_pattern_gen.sv`.
- The real cost is the descriptor-format fan-out: `stream_pkg.sv` (descriptor_t)
  -> `apbtodescr.sv` -> `descriptor_engine.sv` -> `scheduler.sv` parse ->
  PeakRDL register map + host descriptor programming -> every DV descriptor
  builder. Keep it additive (append fields, default linear) to avoid regressing
  base STREAM.

### Authoritative spec

The full plan — the `USE_ROW_COL_MAJOR_ADDRESSING` param, the two queued
addr-gens, the variable-length descriptor layout (`desc_type` in chunk 0
selecting 256b legacy vs 512b extended), acceptance criteria, worked cfg
examples, and rejected alternatives — lives in **STREAM TASK-101**:

- `projects/components/stream/TASKS.md` -> "TASK-101: Descriptor-driven
  2D/strided addressing via dma_address_gen (STREAM Extended)"

This file is the pointer from the module's home directory; keep the detailed
descriptor layout in TASK-101 only (single source of truth).

### Tutorial-simplicity note

STREAM is intentionally simplified for teaching (aligned-only, linear,
no circular buffers — see `projects/components/stream/CLAUDE.md` Rule #0.1).
This integration is therefore an explicit **STREAM-Extended**, opt-in-per-
descriptor feature, not a change to base-tutorial behavior.

**Origin:** scoped as a thought experiment (2026-07-04); cross-referenced from
the misc directory (2026-07-05).
