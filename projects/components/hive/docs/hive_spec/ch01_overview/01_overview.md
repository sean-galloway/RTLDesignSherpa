# Chapter 1.1: HIVE System Overview

## 1.1.1 Executive Summary

HIVE (Hierarchical Intelligent Vector Environment) is a distributed control and monitoring subsystem designed to coordinate the RAPIDS DMA engine and Delta Network compute network. The system consists of a hierarchical RISC-V architecture featuring one VexRiscv controller managing global operations and sixteen SERV lightweight cores providing per-tile traffic monitoring and inband descriptor/configuration injection.

**Primary Design Goals:**
- Provide low-latency, inband control for RAPIDS DMA through AXIS-native descriptor injection
- Enable distributed traffic monitoring across the Delta Network compute network
- Support reconfigurable network topologies through virtual configuration switching
- Serve as comprehensive educational platform with complete performance models and modular design

**Target Platforms:**
- **Proof of Concept:** Digilent NexysA7 100T (Xilinx Artix-7)
- **Production Target:** Digilent Genesys2 (Xilinx Kintex-7 325T)
- **Alternative:** Terasic DE10 Standard (Intel Cyclone V SX)

---

## 1.1.2 System Architecture

### Hierarchical Organization

```
┌─────────────────────────────────────────────────────────────┐
│                     HIVE Control Plane                      │
│  ┌────────────────────────────────────────────────────┐    │
│  │         VexRiscv Master Controller (HIVE-C)        │    │
│  │  - Global RAPIDS DMA coordination                  │    │
│  │  - Network reconfiguration management              │    │
│  │  - Performance monitoring aggregation              │    │
│  │  - External host interface (UART/AXI-Lite)        │    │
│  └──────────────────┬─────────────────────────────────┘    │
│                     │ Control Network                       │
│          ┌──────────┴──────────┬──────────────┐           │
│          ▼          ▼          ▼              ▼           │
│  ┌──────────┐ ┌──────────┐ ... ┌──────────┐ (16 tiles)   │
│  │ SERV-0   │ │ SERV-1   │     │ SERV-15  │              │
│  │ Monitor  │ │ Monitor  │     │ Monitor  │              │
│  └────┬─────┘ └────┬─────┘     └────┬─────┘              │
└───────┼────────────┼──────────────────┼───────────────────┘
        │            │                  │
        ▼            ▼                  ▼
┌───────────────────────────────────────────────────────────┐
│              Delta Network (4×4 Mesh)                     │
│   ┌────┬────┬────┬────┐                                  │
│   │T0  │T1  │T2  │T3  │  T = Compute Tile               │
│   ├────┼────┼────┼────┤  Each tile has:                 │
│   │T4  │T5  │T6  │T7  │  - SERV monitor                 │
│   ├────┼────┼────┼────┤  - Compute elements (DSPs)      │
│   │T8  │T9  │T10 │T11 │  - Local BRAM buffers           │
│   ├────┼────┼────┼────┤  - Router/Network Interface     │
│   │T12 │T13 │T14 │T15 │                                  │
│   └────┴────┴────┴────┘                                  │
└───────────────┬───────────────────────────────────────────┘
                ▼
        ┌──────────────┐
        │    RAPIDS    │
        │  DMA Engine  │
        │ (Virtual     │
        │  Tile 16)    │
        └──────────────┘
```

### Key Architectural Features

**1. Hierarchical Control**
- **HIVE-C (Master)**: Single VexRiscv core for global coordination
- **16× SERV Monitors**: Lightweight per-tile controllers
- **Control Network**: Dedicated communication path HIVE-C ↔ SERVs

**2. Inband Control**
- **No Polling**: HIVE-C pushes descriptors via AXIS packets (CDA packets)
- **Low Latency**: ~10-20 cycles vs. 100+ for memory-mapped polling
- **Delta Network Integration**: CDA packets routed to RAPIDS virtual tile 16

**3. Distributed Monitoring**
- **Per-Tile Statistics**: Each SERV tracks local router traffic
- **Autonomous Triggers**: SERVs inject control packets on congestion/errors
- **Aggregation**: HIVE-C collects and analyzes system-wide performance

**4. Reconfigurable Topology**
- **Virtual Contexts**: Pre-loaded routing configurations (systolic, mesh, tree)
- **Fast Switching**: 10-20 cycle context switch latency
- **Workload Optimization**: Match topology to computation pattern

---

## 1.1.3 Position in Delta/RAPIDS/HIVE Ecosystem

```
┌──────────────────────────────────────────────────────────┐
│                      Host System                         │
│              (x86 CPU, ARM SoC, etc.)                    │
└────────────────┬─────────────────────────────────────────┘
                 │ UART / PCIe / AXI
                 ▼
┌──────────────────────────────────────────────────────────┐
│                    HIVE-C Controller                     │
│             (VexRiscv RISC-V @ 100 MHz)                  │
│  ┌────────────────────────────────────────────────┐     │
│  │  Firmware:                                     │     │
│  │  - Parse host commands                         │     │
│  │  - Generate RAPIDS descriptors                 │     │
│  │  - Inject CDA packets to Delta Network         │     │
│  │  - Aggregate SERV statistics                   │     │
│  │  - Manage network reconfiguration              │     │
│  └────────────────────────────────────────────────┘     │
└──────────┬───────────────────────────────┬───────────────┘
           │ CDA packets (AXIS)            │ Control Network
           │ TUSER=2'b01                   │ to SERVs
           ▼                               ▼
┌────────────────────────┐    ┌──────────────────────────┐
│   Delta Network        │    │   16× SERV Monitors      │
│   Routes CDA packets   │◄───┤   - Traffic counters     │
│   to RAPIDS (tile 16)  │    │   - Congestion detection │
│                        │    │   - Packet injection     │
└──────────┬─────────────┘    └──────────────────────────┘
           │ CDA → RAPIDS
           │ PKT_DATA ↔ Tiles
           ▼
┌──────────────────────────────────────────────────────────┐
│                    RAPIDS DMA Engine                     │
│                    (Virtual Tile 16)                     │
│  ┌────────────────────────────────────────────────┐     │
│  │  Descriptor Engine:                            │     │
│  │  - Receives CDA packets from HIVE-C            │     │
│  │  - Parses 256-bit descriptors                  │     │
│  │  - Executes MM2S / S2MM transfers              │     │
│  └────────────────────────────────────────────────┘     │
└──────────┬───────────────────────────────┬───────────────┘
           │ AXI4                           │ AXIS PKT_DATA
           ▼                               ▼
   ┌──────────────┐              ┌─────────────────────┐
   │ DDR Memory   │              │ Compute Tiles 0-15  │
   │ (Activations,│              │ (DSP MACs, BRAM)    │
   │  Weights,    │              │                     │
   │  Results)    │              └─────────────────────┘
   └──────────────┘
```

### Control Flow Example: Matrix Multiply

**Phase 1: Setup (HIVE-C)**
1. Host sends "matmul layer N, tiles 0-7" command
2. HIVE-C switches Delta Network to mesh mode (if needed)
3. HIVE-C generates MM2S descriptors (DDR → Tiles)
4. HIVE-C generates S2MM descriptors (Tiles → DDR)

**Phase 2: Descriptor Injection (HIVE-C → RAPIDS)**
1. HIVE-C formats 256-bit descriptor packets
2. Sends as CDA packets (TUSER=2'b01, TDEST=16)
3. Delta Network routes to RAPIDS virtual tile 16
4. RAPIDS descriptor engine queues descriptors

**Phase 3: Data Movement (RAPIDS → Tiles)**
1. RAPIDS executes MM2S descriptors
2. Reads activations from DDR via AXI4
3. Sends as PKT_DATA (TUSER=2'b00) via AXIS
4. Delta Network routes to target tiles (TDEST=0-7)

**Phase 4: Computation (Tiles)**
1. Compute elements perform MACs
2. Generate result packets
3. Send as PKT_DATA with TID=source_tile_id
4. Network Interface enforces correct TID (security)

**Phase 5: Result Collection (Tiles → RAPIDS)**
1. Delta Network routes PKT_DATA to RAPIDS (TDEST=16)
2. RAPIDS S2MM channels receive data (TID → Channel mapping)
3. RAPIDS writes results to DDR via AXI4
4. Completion interrupt to HIVE-C

**Phase 6: Monitoring (SERV → HIVE-C)**
1. SERV monitors track packet counts, buffer occupancy
2. Detect congestion if buffer > 75%
3. Send PKT_STATUS packets to HIVE-C
4. HIVE-C aggregates statistics, adjusts scheduling

---

## 1.1.4 HIVE Virtual Tile Addressing

HIVE-C is addressed as **Virtual Tile 17** in the Delta Network topology:

```
Delta Network 4×4 Physical Mesh (Tiles 0-15)
┌────┬────┬────┬────┐
│ T0 │ T1 │ T2 │ T3 │  Row 0
├────┼────┼────┼────┤
│ T4 │ T5 │ T6 │ T7 │  Row 1
├────┼────┼────┼────┤
│ T8 │ T9 │T10 │T11 │  Row 2
├────┼────┼────┼────┤
│T12 │T13 │T14 │T15 │  Row 3
└────┴────┴────┴────┘
         │           │
         ▼           ▼
Virtual Tile 16   Virtual Tile 17
   (RAPIDS)         (HIVE-C)
    DMA Engine      Master Controller
```

**Routing Implications:**
- **To RAPIDS:** TDEST = 16 routes packets to RAPIDS DMA
- **To HIVE-C:** TDEST = 17 routes status packets to HIVE-C
- **From HIVE-C:** CDA packets (TUSER=2'b01) automatically routed to RAPIDS
- **From Tiles:** PKT_STATUS (TUSER=2'b11) automatically routed to HIVE-C

---

## 1.1.5 Packet Type Usage by Component

| Component | Sends | Receives | Purpose |
|-----------|-------|----------|---------|
| **HIVE-C** | CDA (2'b01), PKT_CONFIG (2'b10) | PKT_STATUS (2'b11) | Descriptor injection, network config, monitoring |
| **RAPIDS** | PKT_DATA (2'b00) | CDA (2'b01), PKT_DATA (2'b00) | DMA data transfers |
| **Compute Tiles** | PKT_DATA (2'b00) | PKT_DATA (2'b00), PKT_CONFIG (2'b10) | Computation, reconfiguration |
| **SERV Monitors** | PKT_STATUS (2'b11), PKT_CONFIG (2'b10) | PKT_CONFIG (2'b10) | Traffic reporting, tile control |
| **Delta Routers** | - | PKT_CONFIG (2'b10) | Routing table updates |

**Validation Rules:**
- HIVE-C **never sends** PKT_DATA or PKT_STATUS
- RAPIDS **never sends** CDA, PKT_CONFIG, or PKT_STATUS
- Compute tiles **never send** CDA, PKT_CONFIG, or PKT_STATUS
- SERV monitors can send PKT_STATUS and PKT_CONFIG only

---

## 1.1.6 Educational Platform Features

HIVE is designed as a comprehensive learning platform:

**1. Complete Performance Models**
- SimPy analytical models for NoC, DMA, monitoring overhead
- "What-if" analysis with parameter sweeps
- Validation: Predicted vs. actual hardware performance

**2. Modular Architecture**
- Every component has standardized interfaces
- Components can be replaced without system redesign
- Gradual complexity: Start with 2×2 mesh, scale to 4×4

**3. Comprehensive Documentation**
- Architecture guides with design rationale
- API reference for firmware development
- Tutorials for common use cases
- Performance tradeoff analysis

**4. Verification Infrastructure**
- Unit tests for every RTL module (CocoTB)
- Integration tests for multi-component scenarios
- Formal verification for critical properties
- Hardware-in-loop testing on FPGA

**5. Interactive Learning Tools**
- Web-based visualizer for packet flow
- Jupyter notebooks for model exploration
- Example workloads (matmul, convolution, reduction)
- Synthetic traffic patterns (uniform, hotspot, transpose)

---

**Next:** [Architectural Requirements](02_architectural_requirements.md)

**Back to:** [Index](../hive_index.md)
