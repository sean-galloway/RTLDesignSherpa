# TASK-004: Integrate axi_monitor in AXI4 Slave Read

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Complete (2025-10-04)
**Owner:** seang
**Completed In:** Commit c9a60f6

**Description:**
Integrate the validated axi_monitor_base into the AXI4 slave read monitor wrapper.

**Completed Work:**
- Integrated axi_monitor_filtered into `axi4_slave_rd_mon.sv`
- Monitor instantiation (slave-side perspective)
- Signal connections for slave AR, R channels
- Slave-specific monitoring behavior documented
- Tests passing: `test_axi4_slave_rd_mon.py`
- Monitoring from slave perspective verified

---
