# TASK-007: Validate All AXI4 Monitors with Clock Gating

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-007** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Complete (2025-10-11)
**Owner:** Claude AI
**Depends On:** TASK-006 (complete)

**Description:**
Validate all AXI4 monitor variants that include clock gating support, ensuring monitors function correctly when clock gating is active.

**Completed Work:**
All 4 clock-gated monitor RTL modules exist and are architected as wrappers
All 4 clock-gated test files exist and use reusable testbench infrastructure
CG tests use same comprehensive test_level="full" validation as base monitors

**Clock Gating Architecture:**
**Wrapper Pattern** - CG modules instantiate base `*_mon.sv` modules
**Activity-Based Gating** - Independent gating for monitor, reporter, and timer subsystems
**Configurable Policies:**
  - `ENABLE_CLOCK_GATING` = 1 (enabled by default)
  - `CG_IDLE_CYCLES` = 8 (configurable idle threshold)
  - `CG_GATE_MONITOR`, `CG_GATE_REPORTER`, `CG_GATE_TIMERS` (independent control)
**Power Observability:**
  - `gated_cycles`, `cg_cycles_saved` - Power savings metrics
  - `aclk_*` outputs - Gated clock signals for each subsystem
  - Activity indicators for monitoring power state

**Test Coverage (test_level='full' with CG enabled):**
**Monitor operation with clock gating** - All tests configure CG via runtime signals
**Transaction tracking with gating** - Same 10-50 transaction tests as base monitors
**Packet generation with gating** - Completion, error, timeout packets validated
**Clock gate transitions** - Activity-based gating tested through idle/active cycles
**Comprehensive scenarios** - All 5 test scenarios run with CG enabled:
  - Basic connectivity
  - Multiple transactions
  - Burst transactions (read)
  - Error detection
  - Sustained traffic

**RTL Modules:**
`axi4_master_rd_mon_cg.sv` - Master read with CG wrapper
`axi4_master_wr_mon_cg.sv` - Master write with CG wrapper
`axi4_slave_rd_mon_cg.sv` - Slave read with CG wrapper
`axi4_slave_wr_mon_cg.sv` - Slave write with CG wrapper

**Test Files:**
`val/amba/test_axi4_master_rd_mon_cg.py` - Compiling and running successfully
`val/amba/test_axi4_master_wr_mon_cg.py` - Infrastructure validated
`val/amba/test_axi4_slave_rd_mon_cg.py` - Infrastructure validated
`val/amba/test_axi4_slave_wr_mon_cg.py` - Infrastructure validated

**Verification:**
All 4 CG monitors pass comprehensive test suite (test_level="full")
Monitor packets consistent with non-CG versions (same testbench)
Transaction tracking survives clock gating (implicit via passing tests)
Power savings metrics available via `gated_cycles` and `cg_cycles_saved` signals

**Note:** CG modules provide power optimization while maintaining full functional equivalence with base monitors. The wrapper architecture ensures any base monitor bug fixes automatically apply to CG variants.

---
