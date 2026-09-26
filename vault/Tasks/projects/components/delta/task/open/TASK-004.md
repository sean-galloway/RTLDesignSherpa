# TASK-004: Network Interface RTL Implementation

> Migrated 2026-09-25 from `projects/components/delta/TASKS.md`
> as **TASK-004** (tooling TOOL-001), ID unchanged. Classified against the
> tree, not its Status line.

**Status:** Planned
**Priority:** P0
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Implement the network interface module that converts AXI transactions to Delta packets.

**Acceptance Criteria:**
- [ ] Implement ni_ingress.sv (AXI → Delta packet conversion)
- [ ] Implement ni_egress.sv (Delta packet → AXI conversion)
- [ ] Implement ni_credit_manager.sv (flow control)
- [ ] Implement delta_network_interface.sv (top-level)
- [ ] Add packet fragmentation/reassembly logic
- [ ] Verify synthesizability

**Dependencies:**
- TASK-003 (Router implementation)

**Related Files:**
- `rtl/delta/delta_network_interface.sv`
- `rtl/delta/ni_ingress.sv`
- `rtl/delta/ni_egress.sv`
- `rtl/delta/ni_credit_manager.sv`

---
