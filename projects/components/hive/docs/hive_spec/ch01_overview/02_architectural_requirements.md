# Chapter 1.2: Architectural Requirements

## 1.2.1 Functional Requirements

### FR-1: RAPIDS DMA Control
- **FR-1.1**: HIVE-C must successfully control RAPIDS DMA via inband descriptors
- **FR-1.2**: Descriptor injection through Delta Network as CDA packets (TUSER=2'b01)
- **FR-1.3**: Descriptor format: 256-bit structure with source/dest addresses, length, control flags
- **FR-1.4**: Support multi-level priority queue scheduler (4 priority levels)
- **FR-1.5**: Channel-aware descriptor programming with Tile ID → RAPIDS S2MM Channel mapping

### FR-2: Distributed Traffic Monitoring
- **FR-2.1**: 16 SERV monitors must accurately track per-tile traffic
- **FR-2.2**: Real-time metrics: buffer occupancy, packet counts, congestion flags
- **FR-2.3**: Autonomous trigger conditions: congestion, errors, periodic reporting
- **FR-2.4**: Aggregate traffic statistics from all SERV monitors to HIVE-C
- **FR-2.5**: Configurable monitoring intervals and thresholds

### FR-3: Network Reconfiguration
- **FR-3.1**: Configuration switching must complete within 25 cycles
- **FR-3.2**: Support minimum 4 virtual configuration contexts (systolic, mesh, tree, custom)
- **FR-3.3**: Atomic context switching without packet loss
- **FR-3.4**: Per-tile independent configuration via PKT_CONFIG packets
- **FR-3.5**: Graceful quiesce and resume protocol

### FR-4: Packet Routing
- **FR-4.1**: All packet types correctly routed based on TUSER[1:0] encoding
- **FR-4.2**: PKT_DATA (2'b00) routed through Delta Network to compute tiles
- **FR-4.3**: CDA packets (2'b01) routed to RAPIDS descriptor engine (virtual tile 16)
- **FR-4.4**: PKT_CONFIG (2'b10) routed to tile configuration registers
- **FR-4.5**: PKT_STATUS (2'b11) routed to HIVE-C monitoring aggregator (virtual tile 17)
- **FR-4.6**: Zero packet loss under normal operation

### FR-5: TID Enforcement
- **FR-5.1**: Network Interface must automatically override TID with local tile ID for PKT_DATA
- **FR-5.2**: Prevent tile ID spoofing (security/correctness requirement)
- **FR-5.3**: RAPIDS receives accurate TID for S2MM channel routing
- **FR-5.4**: SERV packets (CONFIG, STATUS) pass TID through unchanged

---

## 1.2.2 Performance Requirements

### PR-1: System Frequency
- **PR-1.1**: System frequency ≥ 100 MHz on NexysA7 100T (proof of concept)
- **PR-1.2**: Target frequency ≥ 150 MHz for optimized design
- **PR-1.3**: SERV monitors: 50-100 MHz (lower frequency acceptable)
- **PR-1.4**: Clock domain crossing properly handled for multi-domain operation

### PR-2: Latency Targets
- **PR-2.1**: Descriptor injection latency < 30 cycles (HIVE-C → RAPIDS)
- **PR-2.2**: CDA packet latency through Delta Network: ~10-20 cycles
- **PR-2.3**: Configuration switching latency: 10-20 cycles (deterministic)
- **PR-2.4**: Congestion detection trigger within 10 cycles
- **PR-2.5**: Status packet generation latency < 5 cycles

### PR-3: Throughput
- **PR-3.1**: Delta Network throughput ≥ 80% of theoretical maximum
- **PR-3.2**: SERV monitoring overhead < 5% of compute time
- **PR-3.3**: Configuration switching overhead < 1% for workloads with 1000+ cycle phases
- **PR-3.4**: Descriptor processing rate: continuous operation without stalls

### PR-4: Resource Budget (NexysA7 100T)
- **PR-4.1**: Total HIVE logic ≤ 14,100 LUTs
- **PR-4.2**: Total HIVE registers ≤ 11,524 FFs
- **PR-4.3**: Total HIVE BRAM ≤ 62 blocks (36Kb each)
- **PR-4.4**: Zero DSP blocks consumed by HIVE (all DSPs available for compute)
- **PR-4.5**: Leave ≥ 49,300 LUTs and 73 BRAM blocks available for compute/RAPIDS

| Component | LUTs | FFs | DSPs | BRAM (36Kb) |
|-----------|------|-----|------|-------------|
| VexRiscv Master (HIVE-C) | 1,400 | 900 | 0 | 8 (256KB inst/data) |
| 16× SERV Monitors | 2,000 | 2,624 | 0 | 16 (32KB each) |
| Control Network Infrastructure | 1,200 | 800 | 0 | 4 |
| Configuration Registers & Logic | 1,500 | 1,200 | 0 | 2 |
| **HIVE Subtotal** | **14,100** | **11,524** | **0** | **62** |
| Available for Compute/RAPIDS | 49,300 | - | 240 | 73 |

---

## 1.2.3 Educational Requirements

### ER-1: Performance Modeling
- **ER-1.1**: SimPy models must predict hardware performance within ±10%
- **ER-1.2**: Provide complete analytical models for NoC, DMA, monitoring overhead
- **ER-1.3**: "What-if" analysis capability with parameter sweeps
- **ER-1.4**: Validation: Predicted vs. actual hardware performance comparison

### ER-2: Test Coverage
- **ER-2.1**: 100% of RTL modules have passing unit tests (CocoTB)
- **ER-2.2**: Coverage target: 100% line, 95%+ branch
- **ER-2.3**: Integration tests for multi-component scenarios
- **ER-2.4**: System-level tests with realistic workloads
- **ER-2.5**: Hardware-in-loop testing on FPGA

### ER-3: Documentation
- **ER-3.1**: Complete API documentation with examples
- **ER-3.2**: Minimum 5 tutorials covering common use cases
- **ER-3.3**: Architecture guides with design rationale
- **ER-3.4**: Performance tradeoff analysis with quantified metrics
- **ER-3.5**: Interface protocol specifications (AXIS, packet formats)

### ER-4: Modularity
- **ER-4.1**: Modular design allows component replacement without system redesign
- **ER-4.2**: Standardized interfaces for all components
- **ER-4.3**: Gradual complexity: Support 2×2 mesh scaling to 4×4
- **ER-4.4**: Configuration hooks for experimentation (parameters, tunables)

---

## 1.2.4 Interface Requirements

### IR-1: HIVE-C Interfaces
- **IR-1.1**: External UART/AXI4-Lite interface for host communication
- **IR-1.2**: AXIS master for CDA packet injection to Delta Network
- **IR-1.3**: Control network master for SERV communication
- **IR-1.4**: Memory-mapped access to RAPIDS, Delta, SERV status registers

### IR-2: SERV Monitor Interfaces
- **IR-2.1**: AXIS interface for packet injection (PKT_CONFIG, PKT_STATUS)
- **IR-2.2**: Control network slave for HIVE-C communication
- **IR-2.3**: Router monitoring signals (buffer occupancy, packet counts)
- **IR-2.4**: Memory-mapped control registers

### IR-3: Delta Network Integration
- **IR-3.1**: Virtual Tile 17 addressing for HIVE-C in Delta Network topology
- **IR-3.2**: AXIS packet routing based on TUSER[1:0] encoding
- **IR-3.3**: TID field usage: source tile ID (4 bits for 16 tiles)
- **IR-3.4**: TDEST field usage: destination tile ID (0-15 compute, 16 RAPIDS, 17 HIVE-C)

### IR-4: Control and Status
- **IR-4.1**: Configuration register bank for network mode selection
- **IR-4.2**: Status registers for buffer occupancy, packet counts, errors
- **IR-4.3**: Interrupt signals for completion, congestion, errors
- **IR-4.4**: Debug/trace interfaces for signal capture

---

## 1.2.5 Security and Reliability Requirements

### SR-1: Tile ID Enforcement
- **SR-1.1**: Hardware-enforced TID override for compute element packets
- **SR-1.2**: Prevent malicious or erroneous tile ID spoofing
- **SR-1.3**: Guarantee correct S2MM channel routing at RAPIDS

### SR-2: Error Detection
- **SR-2.1**: Parity checking on AXIS packets
- **SR-2.2**: Protocol violation detection (invalid TUSER, TDEST combinations)
- **SR-2.3**: Buffer overflow/underflow detection
- **SR-2.4**: Timeout detection for stuck operations

### SR-3: Error Handling
- **SR-3.1**: Error status packet generation on detection
- **SR-3.2**: Graceful degradation on single component failure
- **SR-3.3**: Configurable error response policies (halt, throttle, report)
- **SR-3.4**: Error logging for post-mortem analysis

---

## 1.2.6 Expansion Requirements

### XR-1: Scalability (Future)
- **XR-1.1**: Support scaling to 8×8 mesh (64 tiles) on Kintex-7 325T
- **XR-1.2**: Hierarchical control with multiple VexRiscv cores
- **XR-1.3**: Higher clock frequencies (150-200 MHz)
- **XR-1.4**: Additional routing contexts (up to 8 total)

### XR-2: Feature Extensions (Future)
- **XR-2.1**: Adaptive routing based on congestion
- **XR-2.2**: Quality-of-Service guarantees (bandwidth, latency)
- **XR-2.3**: Fault tolerance with dynamic rerouting
- **XR-2.4**: Machine learning for traffic prediction

---

**Next:** [Clocks and Reset](03_clocks_and_reset.md)

**Back to:** [Index](../hive_index.md) | [Overview](01_overview.md)
