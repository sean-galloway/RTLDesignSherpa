<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Chapter 2.0: Block Overview

## 2.0.1 Component Organization

HIVE consists of four primary functional blocks that work together to provide distributed control and monitoring for the RAPIDS/Delta Network system:

```
HIVE System Architecture
┌─────────────────────────────────────────────────────────────┐
│                     HIVE Control Plane                      │
│  ┌────────────────────────────────────────────────────┐    │
│  │   Block 1: HIVE-C Master Controller (VexRiscv)    │    │
│  │   - Global coordination                            │    │
│  │   - Descriptor scheduling                          │    │
│  │   - Performance aggregation                        │    │
│  └──────────────────┬─────────────────────────────────┘    │
│                     │ Block 3: Control Network              │
│          ┌──────────┴──────────┬──────────────┐           │
│          ▼          ▼          ▼              ▼           │
│  ┌──────────┐ ┌──────────┐ ... ┌──────────┐ (16×)        │
│  │ Block 2: │ │ Block 2: │     │ Block 2: │              │
│  │ SERV-0   │ │ SERV-1   │     │ SERV-15  │              │
│  │ Monitor  │ │ Monitor  │     │ Monitor  │              │
│  └────┬─────┘ └────┬─────┘     └────┬─────┘              │
│       │            │                 │                     │
│       │  Block 4: Configuration Manager                    │
│       │  - Virtual context storage                         │
│       │  - Topology switching                              │
│       └────────────┴──────────────────┘                    │
└─────────────────────────────────────────────────────────────┘
         │ AXIS Packets (CDA, PKT_CONFIG, PKT_STATUS)
         ▼
    Delta Network (4×4 Mesh) + RAPIDS DMA Engine
```

---

## 2.0.2 Resource Budget (NexysA7 100T)

### FPGA Target: Xilinx Artix-7 XC7A100T-1CSG324C

**Total Available Resources:**
- **LUTs:** 63,400
- **Flip-Flops:** 126,800
- **DSP Blocks:** 240
- **BRAM (36Kb):** 135

### HIVE Resource Allocation

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| **Block 1: HIVE-C Controller** | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| **Block 2: SERV Monitors (16×)** | 2,000 | 2,624 | 0 | 16 | 125 LUTs per SERV |
| **Block 3: Control Network** | 1,200 | 800 | 0 | 4 | HIVE-C ↔ SERV comm |
| **Block 4: Configuration Manager** | 1,500 | 1,200 | 0 | 2 | Virtual contexts |
| **HIVE Subtotal** | **14,100** | **11,524** | **0** | **62** | 22% LUT, 46% BRAM |
| **Available for Compute/RAPIDS** | 49,300 | 115,276 | 240 | 73 | Remaining resources |
| **Total Budget** | **63,400** | **126,800** | **240** | **135** | 100% |

**Key Design Constraints:**
- HIVE consumes **zero DSP blocks** (all 240 DSPs available for compute)
- HIVE uses **46% of BRAM** (memory-intensive for instruction/data storage)
- HIVE uses **22% of LUTs** (control logic overhead acceptable)
- Leaves **78% of logic resources** for RAPIDS and Delta Network compute elements

---

## 2.0.3 Block 1: HIVE-C Master Controller

### Overview
VexRiscv RISC-V processor serving as global coordinator for the HIVE system.

### Key Specifications
- **Core:** VexRiscv "Small" configuration
- **ISA:** RV32IM (32-bit, Integer + Multiply/Divide, no Compressed, no FP)
- **Pipeline:** 5-stage pipeline
- **Frequency:** 100 MHz (proof of concept), 150+ MHz (optimized)
- **Memory:**
  - 32KB instruction memory (tightly-coupled BRAM)
  - 32KB data memory (tightly-coupled BRAM)
- **Interfaces:**
  - External UART/AXI4-Lite slave (host commands)
  - AXIS master (CDA packet injection to RAPIDS)
  - Control network master (SERV communication)

### Responsibilities
1. Parse high-level transfer commands from host
2. Generate RAPIDS DMA descriptors (256-bit CDA packets)
3. Inject descriptors into Delta Network via AXIS interface (TUSER=2'b01, TDEST=16)
4. Aggregate traffic statistics from 16 SERV monitors
5. Manage network reconfiguration sequences
6. Handle interrupt routing and exception processing

### Performance Targets
- **Descriptor Injection Latency:** < 30 cycles (HIVE-C → RAPIDS)
- **Command Response Time:** < 1 µs @ 100 MHz
- **Monitoring Aggregation:** < 100 cycles for all 16 SERV status reads

**See:** [Chapter 2.1: HIVE-C Controller](01_hive_c_controller.md) for detailed specification

---

## 2.0.4 Block 2: SERV Monitors (16 instances)

### Overview
Lightweight per-tile traffic monitors using SERV bit-serial RISC-V cores.

### Key Specifications (per SERV instance)
- **Core:** SERV (Small Embedded RISC-V)
- **ISA:** RV32I (32-bit, Integer only, minimal configuration)
- **Implementation:** Bit-serial execution (1 bit per cycle)
- **Frequency:** 50-100 MHz
- **Resources per SERV:**
  - 125 LUTs
  - 164 FFs
  - 1 BRAM (2KB instruction + 2KB data memory)
- **Interfaces:**
  - Control network slave (receive commands from HIVE-C)
  - AXIS master (inject PKT_CONFIG, PKT_STATUS packets)
  - Router monitoring signals (buffer occupancy, packet counts)

### Responsibilities (per tile)
1. Monitor local router traffic (packet counts, buffer occupancy)
2. Detect congestion and anomalies (programmable thresholds)
3. Generate inband control packets on trigger conditions
4. Inject configuration updates into local tile
5. Report statistics to HIVE-C via control network
6. Support debug/trace packet injection

### Monitoring Metrics
- **Counters (32-bit, wrapping):**
  - `pkt_rx_count[4]` - Received packets per direction (N/S/E/W)
  - `pkt_tx_count[4]` - Transmitted packets per direction
  - `pkt_local_inject` - Packets injected by local compute element
  - `pkt_local_consume` - Packets consumed by local compute element
  - `buffer_overflow_count` - FIFO overflow events
  - `stall_cycles` - Cycles with valid packet waiting for credits

- **Real-Time Metrics:**
  - `buffer_occupancy[4]` - Current FIFO fill levels (8-bit per direction)
  - `congestion_flag` - Boolean indicating occupancy > threshold
  - `error_flags` - Parity errors, protocol violations

### Performance Targets
- **Monitoring Overhead:** < 5% of compute time
- **Congestion Detection Latency:** < 10 cycles
- **Periodic Reporting Interval:** 1000 cycles (configurable)

**See:** [Chapter 2.2: SERV Monitor](02_serv_monitor.md) for detailed specification

---

## 2.0.5 Block 3: Control Network

### Overview
Dedicated communication infrastructure for HIVE-C ↔ SERV monitor control and status exchange.

### Key Specifications
- **Topology:** Star topology (HIVE-C master, 16 SERV slaves)
- **Bandwidth:** Low bandwidth control network (separate from Delta Network data path)
- **Arbitration:** Round-robin arbiter for SERV → HIVE-C status reporting
- **Protocol:** Simple valid/ready handshaking
- **Data Width:** 32 bits (control commands and status responses)

### Responsibilities
1. Deliver control commands from HIVE-C to individual SERV monitors
2. Aggregate status reports from SERV monitors to HIVE-C
3. Provide reliable, in-order delivery (no packet loss)
4. Handle priority arbitration (urgent alerts vs. periodic statistics)

### Communication Patterns
- **HIVE-C → SERV (Multicast):**
  - Configuration commands (enable/disable monitoring)
  - Threshold updates (congestion, error triggers)
  - Firmware control (soft reset, debug mode)

- **SERV → HIVE-C (Uplink):**
  - Periodic statistics reports (every 1000 cycles)
  - Congestion alerts (immediate on detection)
  - Error notifications (parity, protocol violations)

### Performance Targets
- **Command Delivery Latency:** < 10 cycles
- **Status Aggregation Time:** < 20 cycles for all 16 SERVs
- **Arbitration Fairness:** Round-robin ensures no SERV starvation

**See:** [Chapter 2.3: Control Network](03_control_network.md) for detailed specification

---

## 2.0.6 Block 4: Configuration Manager

### Overview
Manages virtual configuration contexts and network topology switching.

### Key Specifications
- **Virtual Contexts:** 4 pre-loaded routing configurations
  - Context 0: Systolic Mode (nearest-neighbor)
  - Context 1: Packet-Switched Mesh (XY routing)
  - Context 2: Tree Reduction (hierarchical aggregation)
  - Context 3: Custom/Debug (user-programmable)
- **Context Storage:** BRAM-based context memory (routing tables per tile)
- **Switching Protocol:** Atomic context switch with packet draining

### Responsibilities
1. Store multiple virtual configuration contexts
2. Coordinate atomic topology switching across all tiles
3. Manage quiesce protocol (drain in-flight packets)
4. Broadcast configuration updates via PKT_CONFIG packets
5. Verify successful context switch completion

### Switching Sequence
1. HIVE-C issues `CONFIG_PREPARE` command
   - Target tiles flush in-flight packets
   - Routers enter quiescent state (5-10 cycles)

2. HIVE-C broadcasts `SET_ROUTING_MODE` (PKT_CONFIG packet)
   - All tiles simultaneously update mode register
   - Context switch occurs in single cycle

3. HIVE-C issues `CONFIG_ACTIVATE` command
   - Tiles resume operation with new routing
   - Total latency: 10-20 cycles (deterministic)

### Performance Targets
- **Context Switch Latency:** < 25 cycles (including quiesce)
- **Packet Drain Time:** < 10 cycles (worst-case)
- **Switch Overhead:** < 1% for workloads with 1000+ cycle phases

**See:** [Chapter 2.4: Configuration Manager](04_config_manager.md) for detailed specification

---

## 2.0.7 Inter-Block Communication

### HIVE-C ↔ SERV Monitors
- **Path:** Control Network (Block 3)
- **Direction:** Bidirectional
- **Bandwidth:** Low (command/status messages)
- **Latency:** < 10 cycles

### HIVE-C ↔ Delta Network
- **Path:** AXIS interface
- **Direction:** Master (HIVE-C transmits CDA packets)
- **Bandwidth:** High (256-bit descriptors)
- **Latency:** ~10-20 cycles (packet through Delta Network to RAPIDS)

### SERV Monitors ↔ Delta Network
- **Path:** AXIS interface (per SERV)
- **Direction:** Master (SERV transmits PKT_CONFIG, PKT_STATUS)
- **Bandwidth:** Medium (128-bit packets)
- **Latency:** ~10-20 cycles (packet through Delta Network)

### Configuration Manager ↔ Delta Network Routers
- **Path:** PKT_CONFIG packets via Delta Network
- **Direction:** Broadcast (all routers simultaneously)
- **Bandwidth:** Low (infrequent configuration updates)
- **Latency:** < 5 cycles (direct connection)

---

## 2.0.8 Design Hierarchy

### RTL Module Organization

```
hive_top.sv                          # Top-level integration
├── hive_c_controller/
│   ├── vexriscv_wrapper.sv         # VexRiscv instantiation
│   ├── instruction_mem.sv          # 32KB I-mem
│   ├── data_mem.sv                 # 32KB D-mem
│   ├── descriptor_gen.sv           # CDA packet generation
│   └── axis_master.sv              # AXIS TX interface
│
├── serv_monitor/ (16 instances)
│   ├── serv_wrapper.sv             # SERV core instantiation
│   ├── traffic_counter.sv          # Packet/cycle counters
│   ├── trigger_logic.sv            # Congestion/error detection
│   ├── axis_injector.sv            # PKT_CONFIG/STATUS TX
│   └── local_mem.sv                # 2KB I-mem + 2KB D-mem
│
├── control_network/
│   ├── control_router.sv           # Star topology router
│   ├── control_arbiter.sv          # Round-robin arbiter
│   └── control_packetizer.sv       # Command/status framing
│
├── config_manager/
│   ├── config_registers.sv         # Mode selection registers
│   ├── context_memory.sv           # Virtual context storage
│   └── switch_controller.sv        # Atomic switch orchestration
│
└── common/ (shared utilities)
    ├── axis_fifo.sv                # Asynchronous AXIS FIFO
    ├── credit_counter.sv           # Flow control credits
    └── round_robin_arbiter.sv      # Generic arbiter
```

---

## 2.0.9 Verification Strategy

### Block-Level Testing
- **HIVE-C:** CocoTB unit tests for firmware execution, descriptor generation
- **SERV Monitors:** Individual SERV tests for monitoring logic, trigger conditions
- **Control Network:** Arbitration tests, command delivery, status aggregation
- **Configuration Manager:** Context switch tests, atomic switching, quiesce protocol

### Integration Testing
- **HIVE-C + Control Network + SERV:** End-to-end command/status flow
- **Configuration Manager + Delta Network:** Topology switching validation
- **Full HIVE System:** Multi-block scenarios with realistic traffic

### System Testing
- **HIVE + RAPIDS + Delta:** Complete ecosystem validation
- **Performance Model Validation:** SimPy predictions vs. actual hardware
- **Hardware-in-Loop:** FPGA deployment on NexysA7

**Coverage Targets:**
- 100% line coverage (unit tests)
- 95%+ branch coverage (integration tests)
- Realistic workload validation (system tests)

---

**Next:** [HIVE-C Controller](01_hive_c_controller.md)

**Back to:** [Index](../hive_index.md)
