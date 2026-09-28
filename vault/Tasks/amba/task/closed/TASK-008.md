# TASK-008: Create AXIL Monitor (Adapt from AXI4)

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Complete (2025-10-11)
**Owner:** Claude AI
**Depends On:** TASK-001 (complete)

**Description:**
Create AXI4-Lite monitor wrappers by adapting the existing AXI4 monitor pattern with simplified AXIL protocol requirements.

**Current Infrastructure Status:**
**AXIL RTL Modules Exist:** 8 modules (4 base + 4 CG variants)
  - `axil4_master_rd.sv`, `axil4_master_wr.sv`
  - `axil4_slave_rd.sv`, `axil4_slave_wr.sv`
  - CG variants: `*_cg.sv`
  - **Status:** Basic pass-through/skid buffer modules WITHOUT monitoring

**AXIL Test Infrastructure Exists:** 8 test files
  - `val/amba/test_axil4_master_rd.py`, etc.
  - Uses reusable `AXIL4MasterReadTB` testbench classes
  - **Status:** Tests basic AXIL functionality only, NO monitor validation

**What's Missing:**
  - AXIL monitor wrapper modules (`axil4_*_mon.sv`)
  - Monitor integration (instantiation of `axi_monitor_base`)
  - Monitor validation tests

**Key Differences from AXI4:**
- Single-beat transactions only (no bursts: ARLEN=0, AWLEN=0)
- No ID field (or fixed ID=0)
- Simplified state machine (no burst tracking)
- Reduced transaction table size: MAX_TRANSACTIONS = 4-8 (vs 16-32 for AXI4)

**Implementation Approach (Recommended):**
**Option 1 (CHOSEN):** Reuse `axi_monitor_base` with AXIL-specific parameters
  - Follow proven AXI4 monitor pattern
  - Use AXI4 monitor modules as templates
  - Parameters: `AXI_ID_WIDTH=1` (fixed ID=0), `MAX_TRANSACTIONS=8`
  - Simpler instantiation due to no burst signals

**Deliverables:**
- [x] `axil4_master_rd_mon.sv` - Master read with integrated monitor
- [x] `axil4_master_wr_mon.sv` - Master write with integrated monitor
- [x] `axil4_slave_rd_mon.sv` - Slave read with integrated monitor
- [x] `axil4_slave_wr_mon.sv` - Slave write with integrated monitor
- [x] `axil4_*_mon_cg.sv` - Clock-gated variants (4 modules)

**Design Decisions:**
- [x] **Approach:** Reuse `axi_monitor_base` (no separate `axil_monitor_base` needed)
- [ ] **MAX_TRANSACTIONS:** 8 (recommend: sufficient for typical AXIL register access)
- [ ] **Resource utilization:** Should be ~40-50% of AXI4 monitors (simpler protocol)
- [x] **Monitor bus format:** Same 64-bit packet format (protocol field = 0x0 for AXI)

**Success Criteria:**
- [x] All 8 AXIL monitor modules created (4 base + 4 CG)
- [x] Modules compile cleanly (verified via pytest infrastructure)
- [x] Same error detection capabilities (SLVERR, DECERR, timeout)
- [x] Compatible with existing monitor bus infrastructure
- [x] Follow proven AXI4 pattern with AXIL simplifications

**Created Files (2025-10-11):**
- `rtl/amba/axil4/axil4_master_rd_mon.sv` (12KB)
- `rtl/amba/axil4/axil4_master_wr_mon.sv` (12KB)
- `rtl/amba/axil4/axil4_slave_rd_mon.sv` (12KB)
- `rtl/amba/axil4/axil4_slave_wr_mon.sv` (13KB)
- `rtl/amba/axil4/axil4_master_rd_mon_cg.sv` (9.3KB)
- `rtl/amba/axil4/axil4_master_wr_mon_cg.sv` (9.8KB)
- `rtl/amba/axil4/axil4_slave_rd_mon_cg.sv` (9.0KB)
- `rtl/amba/axil4/axil4_slave_wr_mon_cg.sv` (9.8KB)

---
