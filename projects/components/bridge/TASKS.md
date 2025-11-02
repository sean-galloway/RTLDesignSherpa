# Bridge Component - Task List

**Component:** Bridge (APB/AXI Protocol Conversion)
**Last Updated:** 2025-10-19
**Version:** 1.0

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies or issues
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Scheduled for upcoming work
- 🟢 **Complete** - Finished and verified

## Priority Levels

- **P0** - Critical path, blocks other work
- **P1** - High priority, needed for v1.0
- **P2** - Medium priority, nice to have
- **P3** - Low priority, future enhancement

---

## Active Tasks

### TASK-001: Enhance Integration Examples
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Create comprehensive integration examples showing how to use bridge components in real systems.

**Acceptance Criteria:**
- [ ] Create APB-to-AXI integration example (APB master accessing AXI memory)
- [ ] Create AXI-to-APB integration example (AXI master accessing APB peripherals)
- [ ] Document address mapping configuration
- [ ] Add timing diagrams for bridge operation
- [ ] Include CocoTB integration test snippets

**Dependencies:**
- None (RTL already complete)

**Related Files:**
- `docs/bridge_spec/examples/integration_examples.md` (to be created)

---

### TASK-002: Document Common Use Cases
**Status:** 🟡 Planned
**Priority:** P1
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Document common use cases and scenarios where bridge components are needed.

**Acceptance Criteria:**
- [ ] Document "APB peripheral in AXI system" use case
- [ ] Document "Legacy APB master accessing modern AXI memory" use case
- [ ] Document "Mixed protocol SoC integration" use case
- [ ] Add decision guide: "When to use APB-to-AXI vs AXI-to-APB"
- [ ] Include example system architectures

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/use_cases.md` (to be created)

---

### TASK-003: Performance Characterization
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Characterize and document bridge performance (latency, throughput, resource usage).

**Acceptance Criteria:**
- [ ] Measure APB-to-AXI translation latency (best/worst case)
- [ ] Measure AXI-to-APB translation latency (best/worst case)
- [ ] Document throughput limitations
- [ ] Measure FPGA resource usage (LUTs, FFs, BRAMs)
- [ ] Create performance comparison with native protocols

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/performance_analysis.md` (to be created)

---

### TASK-004: Address Translation Documentation
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Document address translation and mapping configuration in detail.

**Acceptance Criteria:**
- [ ] Explain address mapping parameters
- [ ] Document offset/base address configuration
- [ ] Add examples of 1:1 mapping and offset mapping
- [ ] Include address width conversion scenarios
- [ ] Document address alignment requirements

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/address_translation.md` (to be created)

---

### TASK-005: Error Handling Documentation
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Document error propagation and handling across bridge components.

**Acceptance Criteria:**
- [ ] Document how APB errors (PSLVERR) map to AXI errors (BRESP/RRESP)
- [ ] Document how AXI errors map to APB errors
- [ ] Explain timeout handling (if implemented)
- [ ] Add error recovery examples
- [ ] Document error reporting to system

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/error_handling.md` (to be created)

---

### TASK-006: Wavedrom Timing Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create wavedrom JSON files illustrating bridge protocol conversion.

**Acceptance Criteria:**
- [ ] Create apb_to_axi_read.json (APB read → AXI read)
- [ ] Create apb_to_axi_write.json (APB write → AXI write)
- [ ] Create axi_to_apb_read.json (AXI read → APB read)
- [ ] Create axi_to_apb_write.json (AXI write → APB write)
- [ ] Create error_propagation.json (error handling)
- [ ] Generate SVG/PNG from all JSON files
- [ ] Place in docs/bridge_spec/assets/waves/

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/assets/waves/*.json`

---

### TASK-007: PlantUML FSM Diagrams
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create PlantUML state machine diagrams for bridge FSMs.

**Acceptance Criteria:**
- [ ] Create apb_to_axi_bridge_fsm.puml
- [ ] Create axi_to_apb_bridge_fsm.puml
- [ ] Add annotations explaining state transitions
- [ ] Generate PNG/SVG from all PUML files
- [ ] Place in docs/bridge_spec/assets/puml/

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/assets/puml/*.puml`

---

### TASK-008: Block Diagrams and Architecture Images
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create block diagrams and architecture illustrations for bridge documentation.

**Acceptance Criteria:**
- [ ] Create apb_to_axi_bridge_architecture.svg
- [ ] Create axi_to_apb_bridge_architecture.svg
- [ ] Create protocol_handshake_mapping.svg (APB ↔ AXI)
- [ ] Create system_integration_example.svg (bridge in SoC)
- [ ] Place in docs/bridge_spec/assets/images/

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/assets/images/*.svg`

---

### TASK-009: Configuration Guide
**Status:** 🟡 Planned
**Priority:** P2
**Effort:** 1 day
**Owner:** Unassigned

**Description:**
Create guide for configuring bridge parameters for different use cases.

**Acceptance Criteria:**
- [ ] Document all bridge parameters (address width, data width, etc.)
- [ ] Provide configuration examples for common scenarios
- [ ] Explain parameter dependencies and constraints
- [ ] Add configuration checklist
- [ ] Include troubleshooting tips

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/configuration_guide.md` (to be created)

---

### TASK-010: Burst Support Analysis
**Status:** 🟡 Planned
**Priority:** P3
**Effort:** 2 days
**Owner:** Unassigned

**Description:**
Document current burst support and potential enhancements.

**Acceptance Criteria:**
- [ ] Document current burst handling (if any)
- [ ] Analyze AXI burst → APB sequential transaction conversion
- [ ] Document limitations of APB (no native burst support)
- [ ] Propose enhancement for efficient burst handling
- [ ] Add to future enhancements backlog

**Dependencies:**
- None

**Related Files:**
- `docs/bridge_spec/burst_support_analysis.md` (to be created)

---

## Recently Completed Tasks

### ✅ TASK-000: Core Bridge Implementation (Complete - 2025-10-08)
- Implemented APB-to-AXI bridge RTL
- Implemented AXI-to-APB bridge RTL
- Created protocol conversion logic
- Added handshake translation
- Implemented error propagation
- Created comprehensive CocoTB testbenches
- Verified functional operation

### ✅ TASK-001-PREV: Initial Documentation (Complete - 2025-10-10)
- Created PRD.md with design goals
- Created CLAUDE.md with guidance
- Documented bridge architecture
- Added quick reference sections

---

## Future Enhancements (Backlog)

### TASK-011: Replace Hand-Coded Arbiters with Standard Components
**Priority:** P1
**Description:** Replace hand-coded round-robin arbiters with arbiter_round_robin.sv from rtl/common/.
**Rationale:**
- Current Bridge has inline arbitration logic (~40 lines per arbiter)
- arbiter_round_robin.sv with WAIT_GNT_ACK=1 is perfect for valid/ready handshaking
- Proven component (95% test coverage)
- Easier maintenance and consistent with design standards
- Clear migration path to QoS via arbiter_round_robin_weighted.sv
**Implementation:**
- Replace AW/AR per-slave arbiters with arbiter_round_robin instances
- Set WAIT_GNT_ACK=1 to hold grant until handshake completes
- Update Bridge CSV generator to emit arbiter instantiations
- Test with existing Bridge testbenches
**Impact:**
- Reduces code complexity (~40 lines → ~15 lines per arbiter)
- Enables future QoS enhancement (TASK-017)

### TASK-012: AXI Burst Optimization
**Priority:** P3
**Description:** Optimize AXI burst transaction handling by pipelining APB accesses.

### TASK-013: Outstanding Transaction Support
**Priority:** P3
**Description:** Add support for multiple outstanding transactions (requires buffering).

### TASK-013: Timeout Detection
**Priority:** P3
**Description:** Implement configurable timeout counters for hung transactions.

### TASK-014: APB3 to APB4 Bridge
**Priority:** P3
**Description:** Create bridge between APB3 and APB4 protocol versions.

### TASK-015: AXI4 to AXI4-Lite Bridge
**Priority:** P3
**Description:** Create bridge for AXI4 full to AXI4-Lite conversion.

### TASK-016: Async Clock Domain Crossing
**Priority:** P3
**Description:** Add optional async FIFO for APB and AXI on different clock domains.

### TASK-017: Quality of Service (QoS) Support with Aging Counters
**Priority:** P1
**Description:** Add configurable QoS (Quality of Service) support with aging counters to prevent starvation.
**Rationale:**
- Some masters require higher priority (CPU) vs others (debug)
- Proportional bandwidth allocation (DMA gets 4x more than debug)
- **CRITICAL: Must prevent low-priority masters from starving indefinitely**
- Aging counters boost low-QoS request priority over time to guarantee forward progress
**Prerequisites:**
- TASK-011 must be complete (use arbiter_round_robin.sv first)
**Implementation:**
- Replace arbiter_round_robin with arbiter_round_robin_weighted
- Add QoS weight inputs per master (configurable via parameters or runtime)
- **Add aging counter at each master input (alongside AXI skid buffer wrappers)**
  - Counter increments each cycle while request is pending but not granted
  - When counter reaches threshold, boost QoS to maximum priority
  - Reset counter on grant
  - Configurable aging threshold (e.g., 256 cycles = ~2.5μs at 100MHz)
- Update Bridge CSV generator to support QoS weight configuration
- Test with mixed-priority traffic patterns AND starvation scenarios
**QoS Weight Examples:**
- High priority (CPU): base_qos = 8
- Medium priority (DMA): base_qos = 4
- Low priority (debug): base_qos = 1
**Aging Logic:**
```systemverilog
// Per-master aging counter
logic [7:0] aging_counter[NUM_MASTERS];
logic [3:0] effective_qos[NUM_MASTERS];

always_ff @(posedge aclk) begin
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (!aresetn) begin
            aging_counter[m] <= 8'b0;
        end else if (grant_valid && grant[m]) begin
            aging_counter[m] <= 8'b0;  // Reset on grant
        end else if (request[m]) begin
            if (aging_counter[m] < AGING_THRESHOLD) begin
                aging_counter[m] <= aging_counter[m] + 1'b1;
            end
        end
    end
end

// Boost QoS when aged
always_comb begin
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (aging_counter[m] >= AGING_THRESHOLD) begin
            effective_qos[m] = MAX_QOS;  // Boost to highest priority
        end else begin
            effective_qos[m] = base_qos[m];  // Use configured QoS
        end
    end
end
```
**Configuration Parameters:**
```python
enable_aging: bool = True                 # Enable aging counters (recommended)
aging_threshold: int = 256                # Cycles before boost
aging_counter_width: int = 8              # Counter width (max 255 cycles)
base_qos_weights: Dict[str, int] = {      # Per-master base QoS
    'cpu_master': 8,
    'dma_master': 4,
    'debug_master': 1
}
```
**Impact:**
- Enables deterministic bandwidth allocation
- **Guarantees forward progress for all masters (no starvation)**
- Critical for real-time systems and mixed-criticality SoCs
- Area increase: ~10 FFs per master (aging counter) + QoS arbiter logic
**Test Requirements:**
- Verify low-QoS master eventually gets serviced under heavy high-QoS load
- Measure worst-case latency for low-priority requests
- Confirm aging boost works correctly
**See Also:**
- BRIDGE_QOS_STARVATION_PREVENTION.md (detailed design - to be created)

### TASK-018: CAM-Based Response Routing (Optional Enhancement)
**Priority:** P3
**Description:** Add optional CAM-based response routing for complex transaction scenarios.
**Current Implementation:**
- Simple RAM-based ID lookup (ID → Master mapping)
- Assumes unique IDs for concurrent transactions
- Works for 95% of use cases
**CAM Enhancement Scenarios:**
- Same ID outstanding to multiple slaves simultaneously
- Need (ID, Slave) → Master composite key lookup
- Complex transaction interleaving with aggressive ID reuse
**Implementation Options:**
1. Extend existing cam_tag.sv to cam_lookup.sv with data storage
2. Add parameterizable USE_CAM option (0=RAM, 1=CAM)
3. Document trade-offs (area vs flexibility)
**CAM Lookup Module Features:**
- Composite key: {transaction_id, slave_index}
- Data: master_index
- Operations: insert, lookup, free
- Parallel associative search
**Trade-offs:**
- RAM: Simple, fast, small area, assumes unique IDs
- CAM: Flexible, handles ID reuse, 2-3x area increase
**See Also:**
- rtl/common/cam_tag.sv - Existing CAM for tag presence
- Need to extend for (key→data) mapping

### TASK-019: Pipeline FIFOs for High-Performance Crossbars
**Priority:** P3
**Description:** Add configurable pipeline FIFO stages for maximum throughput and timing closure.
**Rationale:**
- Current: Direct arbitration → mux → connection
- High-performance: Arbitration → FIFO → Mux → FIFO → Connection
- Benefits: Better timing closure (+20-50% fmax), higher throughput (100%), burst pipelining
**Use Cases:**
- High clock frequency targets (> 500 MHz)
- Large crossbars (8x8, 16x16) with long routing paths
- Burst-heavy traffic patterns
- Timing closure challenges in complex SoCs
**Implementation:**
- Add post-arbiter FIFO (shallow, depth=2, timing closure)
- Add post-mux FIFO (deeper, depth=4, throughput)
- Use gaxi_fifo_sync from rtl/amba/gaxi/
- Configurable via BridgeConfig parameters
**Configuration Options:**
```python
pipeline_post_arbiter: bool = False   # FIFO after arbitration
pipeline_post_mux: bool = False       # FIFO after muxing
pipeline_depth_arb: int = 2           # Shallow for timing
pipeline_depth_mux: int = 4           # Deeper for throughput
```
**Trade-offs:**
- Latency: +2-4 cycles per FIFO stage
- Throughput: Up to 100% (eliminates combinational stalls)
- Clock Frequency: +20-50% (breaks long combinational paths)
- Area: +10-20% (FIFO resources)
**Recommendation:**
- Default: OFF (minimal latency for most use cases)
- Enable: For high-performance designs or timing closure issues
**See Also:**
- BRIDGE_REFACTOR_PLAN.md - Phase 3 detailed architecture
- rtl/amba/gaxi/gaxi_fifo_sync.sv - FIFO implementation

### TASK-020: Optional Monitor Integration for Observability
**Priority:** P2
**Description:** Add optional integration of AXI/APB monitor components for rich performance tracking, debugging, error detection, and interrupt monitoring.
**Rationale:**
- Bridge is a critical crossbar component with complex transaction routing
- Monitors provide visibility into: errors, performance bottlenecks, protocol violations, transaction flow
- Debug-time observability without impacting production performance (monitors can be disabled)
**Use Cases:**
- **Performance Analysis:** Track latency, throughput, bottlenecks per master/slave
- **Debug:** Identify protocol violations, stalled transactions, timeout conditions
- **Error Detection:** Catch SLVERR, DECERR, orphaned transactions
- **Interrupt Monitoring:** Track error conditions that should trigger system interrupts
**Available Monitor Components:**
- `axi4_master_rd_mon.sv`, `axi4_master_wr_mon.sv` - Master-side monitoring
- `axi4_slave_rd_mon.sv`, `axi4_slave_wr_mon.sv` - Slave-side monitoring
- `apb_monitor.sv` - APB protocol monitoring (if Bridge has APB converters)
**Implementation Options:**
1. **Per-Port Monitors:** Optional monitor per master/slave interface
2. **Internal Crossbar Monitors:** Monitor internal arbitration points
3. **Aggregated Monitor Bus:** Collect all monitor packets to single FIFO output
**Configuration:**
```python
# Add to BridgeConfig
enable_monitoring: bool = False           # Global monitor enable
monitor_masters: List[int] = []           # Which masters to monitor
monitor_slaves: List[int] = []            # Which slaves to monitor
monitor_packet_types: Dict = {            # Which packet types to enable
    'error': True,
    'completion': False,  # High traffic
    'timeout': True,
    'performance': False  # Enable separately for perf analysis
}
```
**Integration Pattern:**
```systemverilog
// Per-master monitor (optional)
if (ENABLE_MONITORING && MONITOR_MASTERS[m]) begin
    axi4_master_wr_mon #(...) u_m${m}_wr_mon (
        // Connect to master interface signals
        .monbus_pkt_valid(mon_master_wr_valid[m]),
        .monbus_pkt_data(mon_master_wr_data[m]),
        .cfg_error_enable(cfg_mon_error_enable),
        .cfg_timeout_enable(cfg_mon_timeout_enable)
    );
end

// Aggregate monitor packets to single output
arbiter_rr_monbus #(.N(NUM_MONITORS)) u_mon_arbiter (
    .i_valid({mon_master_wr_valid, mon_slave_rd_valid, ...}),
    .i_data({mon_master_wr_data, mon_slave_rd_data, ...}),
    .o_valid(bridge_monbus_valid),
    .o_data(bridge_monbus_data)
);
```
**Monitor Bus Output:**
- Standard 64-bit monitor bus format
- Per-packet type header (error, timeout, performance, etc.)
- Can be routed to system-level monitoring infrastructure
**Benefits:**
- **Debug:** Catch issues during integration testing
- **Performance Tuning:** Identify bottlenecks, optimize QoS weights
- **Production Visibility:** Optional runtime monitoring (can disable for area/power)
- **Standard Interface:** Compatible with existing rtl/amba/ monitor ecosystem
**Trade-offs:**
- Area: +5-10% per monitored interface (depending on enabled packet types)
- Minimal performance impact (monitors are passive observers)
- Can be completely compiled out if not used (via parameters)
**Recommendation:**
- Default: OFF (production configs)
- Enable: For development, debug, performance analysis builds
**See Also:**
- `rtl/amba/axi4/*_mon*.sv` - AXI4 monitor modules
- `rtl/amba/apb/apb_monitor.sv` - APB monitor
- `docs/AXI_Monitor_Configuration_Guide.md` - Monitor configuration best practices
- `rtl/amba/shared/arbiter_rr_monbus.sv` - Monitor bus arbiter

---

## Task Dependencies

```
TASK-001 (Integration Examples) - Independent
TASK-002 (Use Cases) - Independent
TASK-003 (Performance) - Independent
TASK-004 (Address Translation) - Independent
TASK-005 (Error Handling) - Independent
TASK-006 (Wavedrom) - Independent
TASK-007 (PlantUML) - Independent
TASK-008 (Block Diagrams) - Independent
TASK-009 (Configuration Guide) - Independent
TASK-010 (Burst Analysis) - Independent
```

---

## Quick Commands

### Run Specification to PDF (when spec exists)
```bash
python bin/md_to_docx.py \
    projects/components/bridge/docs/bridge_spec/bridge_index.md \
    -o projects/components/bridge/docs/Bridge_Specification_v1.0.docx \
    --toc --title-page --pdf
```

### Run Bridge Tests
```bash
# Run all bridge tests
pytest val/bridge/ -v

# Run APB-to-AXI tests
pytest val/bridge/test_apb_to_axi_bridge.py -v

# Run AXI-to-APB tests
pytest val/bridge/test_axi_to_apb_bridge.py -v
```

### Lint Bridge RTL
```bash
verilator --lint-only rtl/bridge/apb_to_axi_bridge.sv
verilator --lint-only rtl/bridge/axi_to_apb_bridge.sv
```

### Generate Wavedrom SVG
```bash
wavedrom-cli -i docs/bridge_spec/assets/waves/apb_to_axi_read.json \
             -s docs/bridge_spec/assets/waves/apb_to_axi_read.svg
```

### Generate PlantUML PNG
```bash
plantuml docs/bridge_spec/assets/puml/apb_to_axi_bridge_fsm.puml
```

### Measure Resource Usage (Vivado)
```bash
# Synthesize with Vivado and report utilization
vivado -mode batch -source scripts/synth_bridge.tcl
```

---

## Common Use Cases

### Use Case 1: APB Peripheral in AXI System
**Scenario:** Legacy APB peripheral (UART, GPIO) needs to be accessed by AXI master (processor).
**Solution:** Use **AXI-to-APB bridge** to convert AXI transactions to APB.

### Use Case 2: APB Master Accessing AXI Memory
**Scenario:** Simple APB-based microcontroller needs to access large AXI memory.
**Solution:** Use **APB-to-AXI bridge** to convert APB transactions to AXI.

### Use Case 3: Mixed Protocol SoC
**Scenario:** SoC with both APB and AXI subsystems requiring communication.
**Solution:** Use appropriate bridge based on master/slave protocol.

---

## Design Notes

### Protocol Conversion Challenges
- **APB → AXI:** APB is simpler, straightforward mapping to AXI
- **AXI → APB:** AXI has more features (bursts, IDs), need careful handling
- **Burst Handling:** APB doesn't support bursts, must convert to sequential transactions
- **Backpressure:** Careful management of ready/valid handshakes

### Performance Considerations
- **Latency:** Bridge adds protocol conversion overhead (typically 2-4 cycles)
- **Throughput:** APB sequential access limits throughput vs native AXI bursts
- **Resource Usage:** Minimal (mostly FSM + address/data registers)

---

**Last Review:** 2025-10-19
**Next Review:** Quarterly or when adding new features
