# TASK-011: Validate All AXIL Monitors with Clock Gating

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-011** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Complete (2025-10-11)
**Owner:** Claude AI
**Depends On:** TASK-008, TASK-009, TASK-010 (all complete)

**Description:**
Validate clock-gated variants of all AXIL monitors following the proven AXI4 CG wrapper pattern.

**Completed Work:**
**Test Files Created:**
  - `val/amba/test_axil4_master_rd_mon_cg.py` - CG master read monitor validation (PASSED)
  - `val/amba/test_axil4_master_wr_mon_cg.py` - CG master write monitor validation (PASSED)
  - `val/amba/test_axil4_slave_rd_mon_cg.py` - CG slave read monitor validation (PASSED)
  - `val/amba/test_axil4_slave_wr_mon_cg.py` - CG slave write monitor validation (PASSED)

**Test Strategy Implemented:**
  - Reused `AXIL4MasterMonitorTB` and `AXIL4SlaveMonitorTB` from TASK-010
  - Configured CG via runtime signals (cfg_cg_enable=1, cfg_cg_idle_threshold=4)
  - Enabled independent gate control (cfg_cg_gate_monitor, cfg_cg_gate_reporter, cfg_cg_gate_timers)
  - Ran same comprehensive test_level="basic" scenarios with CG enabled

**Clock Gating Architecture Validated:**
  - Activity-based clock gating for monitor/reporter/timer subsystems
  - Lower idle threshold (4 cycles) configured for AXIL simpler protocol
  - Independent gate control per subsystem operational
  - Power observability signals available (`gated_cycles`, `cg_cycles_saved`)

**Test Results:**
- **test_axil4_master_rd_mon_cg.py** - PASSED (11 packets, 3650ns)
- **test_axil4_master_wr_mon_cg.py** - PASSED (11 packets, 4870ns)
- **test_axil4_slave_rd_mon_cg.py** - PASSED (11 packets, 3350ns)
- **test_axil4_slave_wr_mon_cg.py** - PASSED (11 packets, 4270ns)

**Key Validation Points:**
- All 4 AXIL CG monitors compile cleanly and pass tests
- Consistent behavior with non-CG versions (same packet counts)
- Same testbench classes reused successfully
- CG configuration runtime-adjustable via cfg_* signals
- Tests confirm CG wrapper doesn't affect monitor functionality

**CG RTL Modules (Created in TASK-008):**
- `axil4_master_rd_mon_cg.sv` - Wraps `axil4_master_rd_mon` with CG logic
- `axil4_master_wr_mon_cg.sv` - Wraps `axil4_master_wr_mon` with CG logic
- `axil4_slave_rd_mon_cg.sv` - Wraps `axil4_slave_rd_mon` with CG logic
- `axil4_slave_wr_mon_cg.sv` - Wraps `axil4_slave_wr_mon` with CG logic

**Success Criteria:**
- All 4 AXIL CG monitors compile and pass tests
- Consistent behavior with non-CG versions (same testbench)
- Clock gating operational (verified via cfg_cg_enable)
- Power savings available (gated_cycles metrics exposed)

---
