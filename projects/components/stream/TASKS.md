# STREAM Component - Task List

**Component:** STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory)
**Last Updated:** 2025-11-11
**Version:** 1.0
**Status:** 95% Complete

---

## Current Status

### ✅ Completed (95%)

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

## Remaining Work (5%)

### TASK-001: APB Configuration Interface
**Status:** 🟡 Planned
**Priority:** P0 (Critical Path)
**Effort:** 1-2 days

**Description:**
Create APB slave interface using PeakRDL for configuration registers.

**Acceptance Criteria:**
- [ ] Generate APB slave from RDL definition
- [ ] 8 channel kick-off registers
- [ ] Global configuration registers
- [ ] Status/completion registers
- [ ] Integrate into stream_core.sv

**Files:**
- `regs/stream_regs.rdl` (to be created)
- `rtl/macro/apb_config.sv` (generated)

---

### TASK-002: Top-Level Wrapper
**Status:** 🟡 Planned
**Priority:** P0 (Critical Path)
**Effort:** 1 day

**Description:**
Create top-level stream_top.sv wrapper with all interfaces.

**Acceptance Criteria:**
- [ ] Instantiate stream_core
- [ ] Instantiate APB config
- [ ] Connect all AXI masters
- [ ] Connect MonBus output
- [ ] Add parameter validation

**Files:**
- `rtl/macro/stream_top.sv` (to be created)

---

### TASK-003: Final Integration Test
**Status:** 🟡 Planned
**Priority:** P0 (Critical Path)
**Effort:** 1 day

**Description:**
Create comprehensive top-level test using stream_top.sv.

**Acceptance Criteria:**
- [ ] Test all 8 channels
- [ ] Test APB configuration
- [ ] Test descriptor chaining
- [ ] Test error handling
- [ ] Verify MonBus outputs

**Files:**
- `dv/tests/macro/test_stream_top.py` (to be created)

---

## Future Enhancements (Post v1.0)

### Enhancement Ideas
- Add alignment fixup logic (STREAM Extended)
- Add circular buffer support
- Add interrupt generation
- Performance optimization for specific use cases
- Additional MonBus event types

---

## Completed Major Milestones

- ✅ **2025-10-19:** Initial RTL structure created
- ✅ **2025-10-28:** AXI engine V2 design complete
- ✅ **2025-11-10:** Parameter unification complete
- ✅ **2025-11-11:** Write engine bubble-free pipeline enhancement
- ✅ **2025-11-11:** AXI transaction completion tracking added
- ✅ **2025-11-11:** All datapath and core tests passing

---

## Notes

**Architecture Stability:** All core blocks are complete and tested. Only configuration interface and top-level wrapper remain.

**Documentation:** Complete microarchitecture documentation available in `docs/stream_spec/`.

**Verification:** Comprehensive test suite with FUB-level and integration tests passing.
