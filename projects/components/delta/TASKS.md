# Delta Component - Task List

**Component:** Delta (Mesh Network-on-Chip)
**Last Updated:** 2025-10-19
**Version:** 0.25

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies or issues
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Scheduled for upcoming work
- 🟢 **Complete** - Finished and verified

## Priority Levels

- **P0** - Critical path, blocks other work
- **P1** - High priority, needed for v0.25
- **P2** - Medium priority, nice to have
- **P3** - Low priority, future enhancement

---

## Active Tasks

### TASK-001: Complete Specification Chapter 4 (Routing Algorithm)
**Status:** 🟠 In Progress
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Complete detailed specification of the X-Y routing algorithm with deadlock avoidance mechanisms.

**Acceptance Criteria:**
- [ ] Document deterministic X-Y routing rules
- [ ] Define virtual channel allocation strategy
- [ ] Specify deadlock detection and prevention
- [ ] Add routing decision flow diagrams
- [ ] Include example routing scenarios

**Dependencies:**
- Chapter 3 (Router Architecture) complete

**Related Files:**
- `docs/delta_spec/ch04_routing/01_routing_algorithm.md`

---

### TASK-002: Complete Specification Chapter 5 (Flow Control)
**Status:** 🟠 In Progress
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document credit-based flow control mechanism and backpressure handling.

**Acceptance Criteria:**
- [ ] Define credit counter mechanism
- [ ] Specify buffer management strategy
- [ ] Document backpressure propagation
- [ ] Add flow control timing diagrams
- [ ] Define credit initialization

**Dependencies:**
- Chapter 4 (Routing Algorithm) complete

**Related Files:**
- `docs/delta_spec/ch05_flow_control/01_credit_mechanism.md`

---

### TASK-003: Router RTL Implementation
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 1 week
**Owner:** Unassigned

**Description:**
Implement the Delta router RTL with input buffers, route computation, virtual channel allocation, and crossbar switch.

**Acceptance Criteria:**
- [ ] Implement router_input_unit.sv (input buffering + route computation)
- [ ] Implement router_vc_allocator.sv (virtual channel allocation)
- [ ] Implement router_switch_allocator.sv (crossbar arbitration)
- [ ] Implement router_crossbar.sv (5×5 crossbar switch)
- [ ] Implement delta_router.sv (top-level integration)
- [ ] Add comprehensive inline comments
- [ ] Verify synthesizability with Verilator

**Dependencies:**
- TASK-001 (Routing Algorithm spec)
- TASK-002 (Flow Control spec)

**Related Files:**
- `rtl/delta/delta_router.sv`
- `rtl/delta/router_input_unit.sv`
- `rtl/delta/router_vc_allocator.sv`
- `rtl/delta/router_switch_allocator.sv`
- `rtl/delta/router_crossbar.sv`

---

### TASK-004: Network Interface RTL Implementation
**Status:** 🟡 Planned
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

### TASK-005: Mesh Topology RTL Implementation
**Status:** 🟡 Planned
**Priority:** P0
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Implement the 4×4 mesh topology with router and network interface instantiation.

**Acceptance Criteria:**
- [ ] Implement delta_mesh_4x4.sv with 16 routers + 16 NIs
- [ ] Add parameterization for mesh dimensions
- [ ] Implement proper router-to-router connections
- [ ] Add X-Y coordinate assignment logic
- [ ] Verify all interconnections

**Dependencies:**
- TASK-003 (Router implementation)
- TASK-004 (Network interface implementation)

**Related Files:**
- `rtl/delta/delta_mesh_4x4.sv`

---

### TASK-006: CocoTB Router Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 3 days
**Owner:** Unassigned

**Description:**
Create comprehensive CocoTB testbench for single router testing.

**Acceptance Criteria:**
- [ ] Create DeltaRouterTB class in bin/CocoTBFramework/tbclasses/delta/
- [ ] Implement packet injection on all 5 ports
- [ ] Test X-Y routing decisions
- [ ] Verify virtual channel allocation
- [ ] Test credit-based flow control
- [ ] Measure router latency
- [ ] Create test_delta_router.py with >90% coverage

**Dependencies:**
- TASK-003 (Router implementation)

**Related Files:**
- `val/delta/test_delta_router.py`
- `bin/CocoTBFramework/tbclasses/delta/delta_router_tb.py`

---

### TASK-007: CocoTB Mesh Integration Testbench
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 4 days
**Owner:** Unassigned

**Description:**
Create end-to-end mesh network testbench with traffic generation.

**Acceptance Criteria:**
- [ ] Create DeltaMeshTB class
- [ ] Implement AXI master/slave BFMs on all 16 NIs
- [ ] Generate uniform random traffic
- [ ] Generate hotspot traffic patterns
- [ ] Measure network throughput and latency
- [ ] Verify deadlock-free operation
- [ ] Create test_delta_mesh_integration.py

**Dependencies:**
- TASK-005 (Mesh topology implementation)
- TASK-006 (Router testbench)

**Related Files:**
- `val/delta/test_delta_mesh_integration.py`
- `bin/CocoTBFramework/tbclasses/delta/delta_mesh_tb.py`

---

### TASK-008: Wavedrom Timing Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create wavedrom JSON files illustrating key Delta NoC operations.

**Acceptance Criteria:**
- [ ] Create packet_injection.json (NI → router)
- [ ] Create routing_decision.json (X-Y routing)
- [ ] Create credit_flow.json (credit-based flow control)
- [ ] Create virtual_channel_allocation.json (VC arbitration)
- [ ] Generate SVG/PNG from all JSON files
- [ ] Place in docs/delta_spec/assets/waves/

**Dependencies:**
- None (can start anytime)

**Related Files:**
- `docs/delta_spec/assets/waves/*.json`

---

### TASK-009: PlantUML FSM Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create PlantUML state machine diagrams for router and NI FSMs.

**Acceptance Criteria:**
- [ ] Create router_input_fsm.puml
- [ ] Create vc_allocator_fsm.puml
- [ ] Create switch_allocator_fsm.puml
- [ ] Create ni_ingress_fsm.puml
- [ ] Create ni_egress_fsm.puml
- [ ] Generate PNG/SVG from all PUML files
- [ ] Place in docs/delta_spec/assets/puml/

**Dependencies:**
- TASK-003 (Router implementation) - for accurate FSMs

**Related Files:**
- `docs/delta_spec/assets/puml/*.puml`

---

### TASK-010: Block Diagrams and Architecture Images
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create block diagrams and architecture illustrations for specification.

**Acceptance Criteria:**
- [ ] Create router_architecture.svg (router internal blocks)
- [ ] Create mesh_topology.svg (4×4 mesh layout)
- [ ] Create packet_format.svg (packet structure)
- [ ] Create ni_architecture.svg (network interface blocks)
- [ ] Create routing_example.svg (X-Y routing visualization)
- [ ] Place in docs/delta_spec/assets/images/

**Dependencies:**
- None (can use draw.io or similar tools)

**Related Files:**
- `docs/delta_spec/assets/images/*.svg`

---

## Recently Completed Tasks

### ✅ TASK-000: Initial Specification Structure (Complete - 2025-10-15)
- Created specification chapter outline (Ch1-5)
- Completed Chapter 1 (Overview)
- Completed Chapter 2 (Router Architecture)
- Completed Chapter 3 (Network Interface)
- Created initial PRD.md and CLAUDE.md
- Established documentation infrastructure

---

## Future Enhancements (Backlog)

### TASK-011: Performance Monitoring Integration
**Priority:** P3
**Description:** Add Delta-specific monitors to AMBA monitor bus for network performance metrics (latency, throughput, congestion).

### TASK-012: Adaptive Routing Support
**Priority:** P3
**Description:** Extend router to support adaptive routing algorithms (not just deterministic X-Y).

### TASK-013: Quality-of-Service (QoS)
**Priority:** P3
**Description:** Add priority levels to packets and implement weighted arbitration in router.

### TASK-014: Larger Mesh Topologies
**Priority:** P3
**Description:** Parameterize mesh size beyond 4×4 (e.g., 8×8, 16×16).

### TASK-015: Fault Tolerance
**Priority:** P3
**Description:** Add link failure detection and rerouting capabilities.

---

## Task Dependencies

```
TASK-001 (Ch4 Routing)
    └─> TASK-003 (Router RTL)
            └─> TASK-005 (Mesh Topology)
            └─> TASK-006 (Router Testbench)
                    └─> TASK-007 (Mesh Integration Test)

TASK-002 (Ch5 Flow Control)
    └─> TASK-003 (Router RTL)

TASK-003 (Router RTL)
    └─> TASK-004 (NI RTL)
            └─> TASK-005 (Mesh Topology)
    └─> TASK-009 (PlantUML FSMs)

TASK-008 (Wavedrom) - Independent
TASK-010 (Block Diagrams) - Independent
```

---

## Quick Commands

### Run Specification to PDF
```bash
python bin/md_to_docx.py \
    projects/components/delta/docs/delta_spec/delta_index.md \
    -o projects/components/delta/docs/Delta_Specification_v0.25.docx \
    --toc --title-page --pdf
```

### Run Router Tests (when available)
```bash
pytest val/delta/test_delta_router.py -v
```

### Run Mesh Integration Tests (when available)
```bash
pytest val/delta/test_delta_mesh_integration.py -v
```

### Lint Router RTL (when available)
```bash
verilator --lint-only rtl/delta/delta_router.sv
```

### Generate Wavedrom SVG
```bash
# Install wavedrom-cli if needed: npm install -g wavedrom-cli
wavedrom-cli -i docs/delta_spec/assets/waves/packet_injection.json \
             -s docs/delta_spec/assets/waves/packet_injection.svg
```

### Generate PlantUML PNG
```bash
# Install plantuml if needed: sudo apt install plantuml
plantuml docs/delta_spec/assets/puml/router_input_fsm.puml
```

---

**Last Review:** 2025-10-19
**Next Review:** Weekly during active development
