<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# STREAM Component - Task List

**Component:** STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory)
**Last Updated:** 2026-07-05
**Version:** 1.0
**Status:** v1.0 Complete (100%)

---

## Current Status

### ✅ Completed (100%)

**Core Blocks:**
- ✅ descriptor_engine.sv - Descriptor fetch and parsing
- ✅ scheduler.sv - Channel scheduling and coordination
- ✅ axi_read_engine.sv - AXI read master with pipelining
- ✅ axi_write_engine.sv - AXI write master with bubble-free pipeline
- ✅ sram_controller.sv - Multi-channel FIFO buffering
- ✅ stream_alloc_ctrl.sv - SRAM allocation control
- ✅ stream_drain_ctrl.sv - SRAM drain control
- ✅ stream_latency_bridge.sv - Request/response latency bridging
- ✅ perf_profiler.sv - Performance monitoring

**Integration:**
- ✅ scheduler_group.sv - Scheduler + descriptor engine integration
- ✅ scheduler_group_array.sv - 8-channel scheduler array
- ✅ stream_core.sv - Complete datapath integration
- ✅ datapath_rd_test.sv - Read path test harness
- ✅ datapath_wr_test.sv - Write path test harness

**Verification:**
- ✅ FUB tests - All functional unit blocks tested
- ✅ Macro tests - Integration tests passing
- ✅ Stream core tests - Full system verification

**Documentation:**
- ✅ PRD.md - Product requirements complete
- ✅ README.md - Quick start guide
- ✅ CLAUDE.md - AI assistance guide
- ✅ docs/stream_spec/ - Complete architecture documentation

---

## Remaining Work

The original v1.0 critical-path tasks (APB configuration interface, top-level
wrapper, and final integration test) are **complete** and shipped — see the
Completed Major Milestones section. The only remaining item is the optional,
post-v1.0 enhancement below (TASK-101).

---

## Future Enhancements (Post v1.0)

### Enhancement Ideas
- Add alignment fixup logic (STREAM Extended)
- Add circular buffer support → **see TASK-101 (dma_address_gen delivers this via wrap masks)**
- Add interrupt generation
- Performance optimization for specific use cases
- Additional MonBus event types
- Descriptor-driven 2D / strided / scatter addressing → **see TASK-101**

---

### TASK-101: Descriptor-driven 2D/strided addressing via dma_address_gen (STREAM Extended)
**Status:** 💡 Idea / thought experiment (scoped, not started)
**Priority:** P3 (post-v1.0 enhancement — opt-in, NOT a base-STREAM fix)
**Effort:** ~1 week (RTL small; descriptor-format fan-out is the bulk)

**Description:**
Replace the scheduler's linear address accumulation with two `dma_address_gen`
instances (one read, one write), with each instance's cfg supplied by the
descriptor. This turns STREAM from contiguous-only into a strided / 2D-tiled /
circular-buffer / reverse / scatter-transpose DMA — the scatter-gather the name
implies — while keeping linear as the default (so base-tutorial behavior and
existing descriptors/tests are unchanged). Respects the tutorial-simplicity
rule: it is an explicit STREAM-Extended feature, opt-in per descriptor.

**Current addressing (what changes):** `scheduler.sv` seeds `r_src_addr`/
`r_dst_addr` from the descriptor and accumulates linearly each burst:
`r_src_addr <= r_src_addr + (sched_rd_beats_done << clog2(DATA_WIDTH/8))`
(and the dst equivalent) → `sched_rd_addr` / `sched_wr_addr`.

**What dma_address_gen provides** (`projects/components/misc/rtl/dma_address_gen.sv`):
`result_addr = base + index_0*stride_0 + index_1*stride_1`, signed strides +
power-of-2 wrap masks → linear / row-major / col-major / circular / reverse /
scatter. 2-stage pipelined, valid/ready (latency-insensitive). Already used
this exact way in `rtl/amba/shared/axi4_master_wr_pattern_gen.sv`. STREAM's
current linear mode is the strict subset `stride_0=xfer·beat_size, stride_1=0,
wrap=0`.

**Acceptance Criteria:**
- [ ] Two `dma_address_gen` in `scheduler.sv`: `u_rd_addr_gen` (base=src_addr) →
      `sched_rd_addr`, `u_wr_addr_gen` (base=dst_addr) → `sched_wr_addr`, driven
      by per-burst index counters, consumed via valid/ready (prefetch one burst
      ahead to hide the 2-cycle latency).
- [ ] Descriptor extended with independent read/write addr-gen cfg
      (`stride_0`, `stride_1`, `wrap_mask_0`, `wrap_mask_1`, index extents) —
      widen 256→512-bit (4→8 words) or a chained addr-mode word.
- [ ] Parse defaults reproduce today's linear behavior bit-for-bit (backward
      compatible; existing descriptors/tests pass unchanged).
- [ ] Independent src/dst cfg validated (e.g. gather-strided→write-contiguous,
      and a 2D transpose swapping inner/outer stride).
- [ ] New-mode tests (2D, wrap/circular, reverse) + full linear regression green
      via `make run-full-parallel`.

**Ripple / fan-out (the real cost — descriptor format):**
`stream_pkg.sv` (descriptor_t) → `apbtodescr.sv` → `descriptor_engine.sv` →
`scheduler.sv` parse → PeakRDL register map + host descriptor programming →
**every DV descriptor builder**. Keep additive (append fields, default linear)
to avoid regressing base STREAM.

**Files:**
- `projects/components/stream/rtl/fub/scheduler.sv` (instantiate 2× addr-gen; replace accumulate)
- `projects/components/stream/rtl/includes/stream_pkg.sv` (descriptor_t fields)
- `projects/components/stream/rtl/fub/{apbtodescr,descriptor_engine}.sv`
- `projects/components/misc/rtl/dma_address_gen.sv` (reused as-is)
- DV descriptor builders + register map/host (fan-out)

**Descriptor layout (Option 1 — CHOSEN): 512-bit extended (8 x 64b)**

Keep the existing 256 bits byte-identical (zero-regression), add a second
256-bit half for independent read/write addr-gen cfg. `addr_mode_en` (bit 208,
in today's reserved field) selects legacy-linear (ignore words 4-7) vs addr-gen.
Read base = `src_addr`, write base = `dst_addr` (no new base fields). Each
direction supplies stride_0/stride_1 (signed byte strides), inner_count
(index_0 extent = beats per row), and wrap0/wrap1 (log2-encoded circular window,
0=off; scheduler expands to a (2^n - 1) mask). Scheduler walks
index_0 = 0..inner_count-1, bumps index_1 each wrap, for `length` total beats.

Words 0-3 [255:0] — UNCHANGED legacy layout:
| Bits      | Field |
|-----------|-------|
| [63:0]    | src_addr  (= READ base) |
| [127:64]  | dst_addr  (= WRITE base) |
| [159:128] | length (total beats) |
| [191:160] | next_descriptor_ptr |
| [192..195]| valid / interrupt / last / error |
| [199:196] | channel_id |
| [207:200] | priority |
| [208]     | addr_mode_en  (0 = legacy linear; ignore words 4-7) |
| [255:209] | reserved |

Words 4-7 [511:256] — NEW addr-gen cfg:
| Bits      | Field           | Notes |
|-----------|-----------------|-------|
| [287:256] | rd_stride_0     | 32b signed byte stride (inner) |
| [319:288] | rd_stride_1     | 32b signed byte stride (outer) |
| [335:320] | rd_inner_count  | 16b — index_0 extent (beats/row) |
| [341:336] | rd_wrap0_log2   | 6b — circular window = 2^n bytes (0=off) |
| [347:342] | rd_wrap1_log2   | 6b |
| [351:348] | reserved        | |
| [383:352] | wr_stride_0     | 32b signed |
| [415:384] | wr_stride_1     | 32b signed |
| [431:416] | wr_inner_count  | 16b |
| [437:432] | wr_wrap0_log2   | 6b |
| [443:438] | wr_wrap1_log2   | 6b |
| [447:444] | reserved        | |
| [511:448] | reserved (64)   | future: 3rd dim / element-size / split rd·wr length |

Worked cfg examples (8-byte beats):
| Pattern | rd cfg | wr cfg |
|---------|--------|--------|
| Legacy linear | addr_mode_en=0 (or s0=8, s1=0) | same |
| 2D tile copy (WxH, row pitch P) | s0=8, s1=P, inner=W | s0=8, s1=P, inner=W |
| Transpose (row-major read -> col-major write) | s0=8, s1=P_src, inner=W | s0=P_dst, s1=8, inner=W |
| Gather-strided -> pack contiguous | s0=STRIDE, s1=0, inner=len | s0=8, s1=0, inner=len |
| Circular src buffer (size 2^K) | s0=8, wrap0_log2=K | s0=8 |
| Reverse read | s0=-8, inner=len | s0=8 |

Rejected alternatives: Option 2 (384b shared rd/wr stride set — half the
storage but no transpose / independent gather-scatter); Option 3 (chained
addr-mode side-descriptor — no base-width change but a 2nd fetch + extra FSM
state). Option 1 chosen because independent rd/wr cfg is what makes STREAM
actually scatter-gather (transpose + gather/scatter need separate src/dst
iteration), at a clean 8x64 fetch with the legacy 256b bit-identical.

**Origin:** scoped as a thought experiment (2026-07-04); RTL core is low-risk
(proven module, linear=subset), descriptor-format change is the wide/mechanical
part. Descriptor layout (Option 1) folded in 2026-07-04.

---

## Completed Major Milestones

- ✅ **2025-10-19:** Initial RTL structure created
- ✅ **2025-10-28:** AXI engine V2 design complete
- ✅ **2025-11-09:** APB configuration interface complete (PeakRDL `stream_regs`) — TASK-001
- ✅ **2025-11-10:** Parameter unification complete
- ✅ **2025-11-11:** Write engine bubble-free pipeline enhancement
- ✅ **2025-11-11:** AXI transaction completion tracking added
- ✅ **2025-11-11:** All datapath and core tests passing
- ✅ **2025-11-24:** Top-level wrapper `stream_top_ch8.sv` complete — TASK-002
- ✅ **2025-11-30:** Final integration tests passing (`test_stream_top*`); v1.0 complete — TASK-003

---

## Notes

**Architecture Stability:** All core blocks, the APB configuration interface, and the top-level wrapper are complete and tested. v1.0 is done; only the optional post-v1.0 enhancement (TASK-101) remains.

**Documentation:** Complete microarchitecture documentation available in `docs/stream_spec/`.

**Verification:** Comprehensive test suite with FUB-level and integration tests passing.
