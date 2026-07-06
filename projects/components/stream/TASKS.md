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
Add strided / 2D-tiled / circular / reverse / scatter-transpose addressing to
STREAM — the scatter-gather the name implies — as an opt-in extension that leaves
the base tutorial engine bit-for-bit unchanged. Gated by a compile-time param and
selected at runtime per descriptor, so both a "pure linear" build and mixed
legacy+extended descriptor chains are supported.

**Gating parameter: `USE_ROW_COL_MAJOR_ADDRESSING`** (compile-time):
- `= 0` — **scheduler unchanged AND `descriptor_engine` unchanged**: linear
  address accumulation, 256-bit descriptors only, base-tutorial behavior
  untouched.
- `= 1` — two `dma_address_gen` FUBs (read + write) drive addressing; the hardware
  accepts **both** 256-bit legacy and 512-bit extended descriptors, chosen at
  runtime per descriptor (see `desc_type` below).

**Design intent — surgical gating.** The param must shut the row/col addressing
path off at one clean, localized point, NOT as `if (param)` conditionals
sprinkled through every module. `param=0` is the base tutorial engine, verbatim.

**Two address generators + queues (enables transpose):**
`u_rd_addr_gen` (base = `src_addr` → `sched_rd_addr`) and `u_wr_addr_gen`
(base = `dst_addr` → `sched_wr_addr`). Independent read/write iteration is what
makes **transpose** (row-major read <-> col-major write) and independent
gather/scatter possible. Each generator's output feeds its own **address FIFO**
so addresses are produced run-ahead of consumption — this hides the 2-stage
addr-gen latency and lets the scheduler pull the next src/dst address the cycle
it needs it.

**Address FIFOs are decoupled from the param.** The FIFOs are usable in legacy
mode (`param=0`) too — they are required for timing in the new mode but are
structurally independent of the row/col feature. Supporting them cleanly carries
its own set of design updates (a separate workstream from the addressing feature),
kept apart so the `param=0` build stays genuinely unchanged.

**Variable-length descriptors (the key design point):** even with the param on,
STREAM keeps **256-bit legacy descriptors** (linear addressing) AND adds
**512-bit extended descriptors** (addr-gen driven). A small **`desc_type`** field
in the FIRST 256-bit chunk selects legacy (1 chunk) vs extended (2 chunks);
`desc_type = 0` decodes to today's behavior bit-for-bit. Consequences:
- **`descriptor_engine.sv`** reads `desc_type` from the first chunk and, for an
  extended descriptor, fetches the **second 256-bit half** (a conditional second
  beat). Legacy descriptors never pay for the extra fetch.
- **`scheduler.sv`** reads `desc_type` and dequeues **two chunks** (extended) or
  **one** (legacy) from the descriptor queue. Mixed chains (some legacy, some
  extended) are supported naturally.

**Current addressing (what param=1 replaces, extended descriptors only):**
`scheduler.sv` seeds `r_src_addr`/`r_dst_addr` and accumulates linearly each burst
`r_src_addr <= r_src_addr + (beats_done << clog2(DATA_WIDTH/8))`. Legacy
descriptors keep this path; extended descriptors take their addresses from the
addr-gen queues instead.

**What dma_address_gen provides** (`projects/components/misc/rtl/dma_address_gen.sv`):
`result_addr = base + index_0*stride_0 + index_1*stride_1`, signed strides +
power-of-2 wrap masks → linear / row-major / col-major / circular / reverse /
scatter. 2-stage pipelined, valid/ready. Already used this exact way in
`rtl/amba/shared/axi4_master_wr_pattern_gen.sv`. Linear is the strict subset
`stride_0=beat_size, stride_1=0, wrap=0`.

**Acceptance Criteria:**
- [ ] `USE_ROW_COL_MAJOR_ADDRESSING=0` builds identically to today (no addr-gen,
      256b descriptors only) — full regression bit-for-bit unchanged.
- [ ] `USE_ROW_COL_MAJOR_ADDRESSING=1`: `u_rd_addr_gen` + `u_wr_addr_gen`, each
      with an address FIFO producing addresses run-ahead; scheduler consumes
      src/dst addresses via valid/ready.
- [ ] `descriptor_engine` detects `desc_type` from the first chunk and
      conditionally fetches the 2nd 256-bit half for extended descriptors.
- [ ] `scheduler` dequeues 1 chunk (legacy) or 2 chunks (extended) per
      `desc_type`; a mixed legacy+extended chain is validated.
- [ ] Extended descriptor carries independent rd/wr addr-gen cfg (`stride_0`,
      `stride_1`, `inner_count`, `wrap0/wrap1_log2`).
- [ ] Transpose validated (row-major read → col-major write) plus gather-strided
      → contiguous, 2D tile, wrap/circular, and reverse.
- [ ] Full linear regression green via `make run-full-parallel` in BOTH param modes.

**Ripple / fan-out (the real cost — descriptor format):**
`stream_pkg.sv` (descriptor_t + `desc_type` + extended half) → `apbtodescr.sv` →
`descriptor_engine.sv` (type detect + conditional 2nd-half fetch) → `scheduler.sv`
(1-vs-2-chunk dequeue + addr-gen instances/queues) → PeakRDL register map + host
descriptor programming → **every DV descriptor builder**. Keep additive
(`desc_type=0` default) so base STREAM is untouched.

**Files:**
- `projects/components/stream/rtl/fub/scheduler.sv` (param, 2× addr-gen + queues, 1/2-chunk dequeue)
- `projects/components/stream/rtl/fub/descriptor_engine.sv` (type detect, conditional 2nd-half fetch)
- `projects/components/stream/rtl/includes/stream_pkg.sv` (`desc_type`, extended descriptor_t)
- `projects/components/stream/rtl/fub/apbtodescr.sv`
- `projects/components/misc/rtl/dma_address_gen.sv` (reused as-is)
- DV descriptor builders + register map/host (fan-out)

**Descriptor layout — variable length (256b legacy / 512b extended):**

Chunk 0 keeps the existing 256 bits byte-identical (zero-regression) except a
small **`desc_type`** field carved from today's reserved region selects legacy vs
extended. Legacy = 1 chunk; extended = chunk 0 + a second 256-bit half carrying
independent rd/wr addr-gen cfg. Read base = `src_addr`, write base = `dst_addr`.
Each direction supplies stride_0/stride_1 (signed byte strides), inner_count
(index_0 extent = beats/row), wrap0/wrap1 (log2 circular window, 0=off; scheduler
expands to a `2^n - 1` mask). Scheduler walks index_0 = 0..inner_count-1, bumps
index_1 each wrap, for `length` total beats.

Chunk 0 [255:0] — UNCHANGED legacy layout (except `desc_type`):
| Bits      | Field |
|-----------|-------|
| [63:0]    | src_addr  (= READ base) |
| [127:64]  | dst_addr  (= WRITE base) |
| [159:128] | length (total beats) |
| [191:160] | next_descriptor_ptr |
| [192..195]| valid / interrupt / last / error |
| [199:196] | channel_id |
| [207:200] | priority |
| [210:208] | desc_type  (0 = legacy 256b / 1 chunk; 1 = extended 512b / 2 chunks; 2-7 reserved) |
| [255:211] | reserved |

Chunk 1 [511:256] — extended only (`desc_type=1`), NEW addr-gen cfg:
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
| Legacy linear | desc_type=0 (256b, 1 chunk) | same |
| 2D tile copy (WxH, row pitch P) | s0=8, s1=P, inner=W | s0=8, s1=P, inner=W |
| Transpose (row-major read -> col-major write) | s0=8, s1=P_src, inner=W | s0=P_dst, s1=8, inner=W |
| Gather-strided -> pack contiguous | s0=STRIDE, s1=0, inner=len | s0=8, s1=0, inner=len |
| Circular src buffer (size 2^K) | s0=8, wrap0_log2=K | s0=8 |
| Reverse read | s0=-8, inner=len | s0=8 |

**Chosen vs rejected:** variable-length (a `desc_type` field + conditional
2nd-chunk fetch) chosen over always-fetch-512 (wastes descriptor bandwidth on
legacy transfers and forces every chain to 512b) and over a shared rd/wr stride
set (no transpose / independent gather-scatter — separate src/dst iteration is
the whole point). The `USE_ROW_COL_MAJOR_ADDRESSING=0` build drops all of it for
the base tutorial.

**Origin:** scoped as a thought experiment (2026-07-04); design corrected
2026-07-05 to variable-length descriptors (256b legacy + 512b extended via
`desc_type`), two queued addr-gens (rd+wr, enabling transpose), gated by
compile-time `USE_ROW_COL_MAJOR_ADDRESSING`.

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
