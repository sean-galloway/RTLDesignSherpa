# TASK-009: Integrate AXIL Monitor in All AXIL Modules

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-009** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Complete (2025-10-11) - MERGED with TASK-008
**Owner:** Claude AI
**Depends On:** TASK-008 (complete)

**Description:**
This task was MERGED with TASK-008. Creating monitor wrappers IS the integration - no additional work needed.

**Result:**
Base AXIL modules exist without monitors: `axil4_master_rd.sv`, etc.
Monitor wrappers now exist: `axil4_master_rd_mon.sv`, `axil4_*_mon.sv` (8 modules)

**Note:** Following the proven AXI4 pattern, monitor modules are standalone wrappers that instantiate base modules + monitoring infrastructure. Users choose either base modules (no monitoring) or monitor modules (with monitoring) at integration time.

**Modules Created (via TASK-008):**
- [x] `axil4_master_rd_mon.sv` - Wraps `axil4_master_rd` + `axi_monitor_filtered`
- [x] `axil4_master_wr_mon.sv` - Wraps `axil4_master_wr` + `axi_monitor_filtered`
- [x] `axil4_slave_rd_mon.sv` - Wraps `axil4_slave_rd` + `axi_monitor_filtered`
- [x] `axil4_slave_wr_mon.sv` - Wraps `axil4_slave_wr` + `axi_monitor_filtered`

**Integration Pattern (completed):**
- [x] Instantiate base AXIL module (`axil4_*`)
- [x] Instantiate `axi_monitor_filtered` with AXIL parameters
- [x] Connect AXIL signals (simplified: no burst/ID signals)
- [x] Wire monitor bus outputs (monbus_valid, monbus_ready, monbus_packet)
- [x] Add monitor configuration signals (cfg_*_enable)
- [x] Document module purpose and AXIL simplifications

**Verification:**
- [x] All 8 modules compile cleanly
- [x] Ready for validation testing in TASK-010

---
