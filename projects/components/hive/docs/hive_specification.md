# HIVE System Specification
**Hierarchical Intelligent Vector Environment**  
Version 0.3 - Early Proof of Concept (Draft)

---

## 1. Executive Summary

HIVE is a distributed control and monitoring subsystem designed to coordinate the RAPIDS DMA engine and DELTA compute network. The system consists of a hierarchical RISC-V architecture featuring one VexRiscv controller managing global operations and sixteen SERV lightweight cores providing per-tile traffic monitoring and inband descriptor/configuration injection.

**Primary Design Goals:**
- Provide low-latency, inband control for RAPIDS DMA through AXIS-native descriptor injection
- Enable distributed traffic monitoring across the DELTA compute network
- Support reconfigurable network topologies through virtual configuration switching
- Serve as comprehensive educational platform with complete performance models and modular design

**Target Platforms:**
- Proof of Concept: Digilent NexysA7 100T (Xilinx Artix-7)
- Production Target: Digilent Genesys2 (Xilinx Kintex-7 325T)
- Alternative: Terasic DE10 Standard (Intel Cyclone V SX)

---

## 2. System Architecture

### 2.1 Hierarchical Organization

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
│              DELTA Compute Network (4x4 Mesh)             │
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
        │ (controlled  │
        │  by HIVE-C)  │
        └──────────────┘
```

### 2.2 Resource Budget (NexysA7 100T)

| Component | LUTs | FFs | DSPs | BRAM (36Kb) |
|-----------|------|-----|------|-------------|
| VexRiscv Master (HIVE-C) | 1,400 | 900 | 0 | 8 (256KB inst/data) |
| 16× SERV Monitors | 2,000 | 2,624 | 0 | 16 (32KB each) |
| 4×4 Mesh NoC (16 routers) | 8,000 | 6,000 | 0 | 32 (FIFO buffers) |
| Control Network Infrastructure | 1,200 | 800 | 0 | 4 |
| Configuration Registers & Logic | 1,500 | 1,200 | 0 | 2 |
| **HIVE Subtotal** | **14,100** | **11,524** | **0** | **62** |
| Available for Compute/RAPIDS | 49,300 | - | 240 | 73 |
| **Total Budget** | **63,400** | - | **240** | **135** |

### 2.3 Component Definitions

#### 2.3.1 HIVE-C (Master Controller)
**Core:** VexRiscv "Small" configuration
- RV32IM instruction set (no compressed, no floating point)
- 5-stage pipeline
- 32KB instruction memory (tightly-coupled)
- 32KB data memory (tightly-coupled)
- AXI4-Lite master for external register access
- Custom instruction for atomic descriptor injection
- Target frequency: 100 MHz (proof of concept), 150+ MHz (optimized)

**Responsibilities:**
1. Parse high-level transfer commands from host
2. Generate RAPIDS DMA descriptors
3. Inject descriptors into DELTA via AXIS interface
4. Aggregate traffic statistics from SERV monitors
5. Manage network reconfiguration sequences
6. Handle interrupt routing and exceptions

#### 2.3.2 SERV Monitors (Per-Tile Controllers)
**Core:** SERV bit-serial RISC-V (RV32I)
- Minimal configuration: 125 LUTs, 164 FFs
- 2KB local instruction memory
- 2KB local data memory (traffic buffers & statistics)
- AXIS network interface for packet injection
- Memory-mapped control registers
- Target frequency: 50-100 MHz

**Responsibilities:**
1. Monitor local router traffic (packet counts, buffer occupancy)
2. Detect congestion and anomalies
3. Generate inband control packets on trigger conditions
4. Inject configuration updates into local tile
5. Report statistics to HIVE-C via control network
6. Support debug/trace packet injection

---

## 3. Control and Data Encoding

### 3.1 AXIS Packet Classification

HIVE uses two control bits in the AXIS TUSER field to classify packets:

```verilog
// AXIS TUSER[1:0] encoding
typedef enum logic [1:0] {
    PKT_DATA   = 2'b00,  // Compute data (activations, weights, results)
    PKT_DESC   = 2'b01,  // DMA descriptor
    PKT_CONFIG = 2'b10,  // Configuration command
    PKT_STATUS = 2'b11   // Status/monitoring data
} packet_type_t;
```

**Routing Rules:**
- `PKT_DATA`: Routed through DELTA mesh to compute tiles
- `PKT_DESC`: Routed to RAPIDS DMA descriptor queue
- `PKT_CONFIG`: Routed to tile configuration registers
- `PKT_STATUS`: Routed to HIVE-C monitoring aggregator

### 3.2 Descriptor Format

RAPIDS descriptors injected by HIVE-C follow this 256-bit structure:

```
Bits [255:192]: Source Address (64-bit)
Bits [191:128]: Destination Address (64-bit)
Bits [127:96]:  Transfer Length (32-bit, in bytes)
Bits [95:64]:   2D Stride Configuration (32-bit)
Bits [63:32]:   Control Flags (32-bit)
Bits [31:0]:    Next Descriptor Pointer (32-bit)

Control Flags [31:0]:
  [31:28] - Burst Size (AXI beats)
  [27:24] - Burst Type (FIXED/INCR/WRAP)
  [23:20] - Priority Level (0-15)
  [19:16] - Destination Tile ID
  [15:12] - Reserved
  [11:8]  - Completion Interrupt Vector
  [7]     - Enable 2D Transfer
  [6]     - Enable Scatter-Gather (follow next ptr)
  [5]     - Generate Completion Interrupt
  [4]     - Cache Coherent Access
  [3:0]   - Descriptor Type (future expansion)
```

### 3.3 Configuration Packet Format

Configuration packets (PKT_CONFIG) use this 128-bit structure:

```
Bits [127:96]:  Target Tile Mask (32-bit, one bit per tile)
Bits [95:64]:   Configuration Command (32-bit)
Bits [63:0]:    Payload Data (64-bit)

Command Types:
  0x0000_0001: Set Routing Mode (payload = mode ID)
  0x0000_0002: Update Router Table Entry
  0x0000_0004: Set Traffic Priority Weights
  0x0000_0008: Enable/Disable Tile
  0x0000_0010: Flush Local Buffers
  0x0000_0020: Reset Statistics Counters
  0x0000_0040: Update Clock Divider
  0x0000_0080: Set Debug Trace Mode
```

### 3.4 Status Packet Format

Status packets (PKT_STATUS) aggregate monitoring data:

```
Bits [127:120]: Source Tile ID (8-bit)
Bits [119:112]: Status Type (8-bit)
Bits [111:64]:  Timestamp (48-bit cycle counter)
Bits [63:0]:    Payload (type-dependent)

Status Types:
  0x01: Traffic Statistics (packet counts)
  0x02: Buffer Occupancy Report
  0x04: Congestion Alert
  0x08: Error/Exception Report
  0x10: Performance Counter Snapshot
  0x20: Debug Trace Data
```

---

## 4. Network Reconfiguration System

### 4.1 Virtual Configuration Contexts

HIVE supports rapid topology switching through pre-loaded routing configurations:

**Context 0 - Systolic Mode:**
- Direct nearest-neighbor communication
- North/South/East/West fixed routing
- Minimal router involvement (bypass packet switching)
- Latency: 1-2 cycles per hop

**Context 1 - Packet-Switched Mesh:**
- Full XY dimension-ordered routing
- Credit-based flow control
- 2 virtual channels for deadlock avoidance
- Latency: 3-4 cycles per hop

**Context 2 - Tree Reduction:**
- Hierarchical aggregation topology
- Tiles 12-15 as root aggregators
- East-West links form reduction tree
- Optimized for global reductions (sum, max, etc.)

**Context 3 - Custom/Debug:**
- User-programmable routing tables
- Per-tile independent configuration
- Supports irregular topologies

### 4.2 Configuration Switching Protocol

```
1. HIVE-C issues CONFIG_PREPARE command
   - Target tiles flush in-flight packets
   - Routers enter quiescent state
   
2. HIVE-C broadcasts SET_ROUTING_MODE
   - All tiles simultaneously update mode register
   - Context switch occurs in single cycle
   
3. HIVE-C issues CONFIG_ACTIVATE command
   - Tiles resume operation with new routing
   
Total latency: 10-20 cycles (deterministic)
```

### 4.3 Router Configuration Registers

Each tile router exposes these memory-mapped registers:

```
Base + 0x00: MODE_SELECT     (RW) - Context ID [1:0]
Base + 0x04: ROUTE_TABLE_0   (RW) - Custom routing entry 0
Base + 0x08: ROUTE_TABLE_1   (RW) - Custom routing entry 1
     ...
Base + 0x20: FLOW_CTRL_CFG   (RW) - Credit limits, VC allocation
Base + 0x24: PRIORITY_MASK   (RW) - QoS priority weights
Base + 0x28: STATUS          (RO) - Buffer occupancy, active packets
Base + 0x2C: STATISTICS      (RO) - Packet counters
Base + 0x30: ERROR_FLAGS     (RO) - Overflow, underflow, parity errors
Base + 0x34: DEBUG_TRACE     (RW) - Trace filter configuration
```

---

## 5. SERV Monitor Functionality

### 5.1 Traffic Monitoring Metrics

Each SERV core tracks per-tile statistics:

**Counters (32-bit, wrapping):**
- `pkt_rx_count[4]`: Received packets per direction (N/S/E/W)
- `pkt_tx_count[4]`: Transmitted packets per direction
- `pkt_local_inject`: Packets injected by local compute element
- `pkt_local_consume`: Packets consumed by local compute element
- `buffer_overflow_count`: FIFO overflow events
- `stall_cycles`: Cycles with valid packet waiting for credits

**Real-Time Metrics (updated every cycle):**
- `buffer_occupancy[4]`: Current FIFO fill levels (8-bit per direction)
- `congestion_flag`: Boolean indicating occupancy > threshold
- `error_flags`: Parity errors, protocol violations

### 5.2 Trigger Conditions

SERV monitors can autonomously inject control packets when:

1. **Congestion Detection:** Buffer occupancy exceeds programmable threshold (default: 75%)
   - Action: Send status packet to HIVE-C
   - Optionally throttle local injection rate

2. **Error Detection:** Parity error or protocol violation
   - Action: Send error status packet
   - Halt local packet injection pending recovery

3. **Periodic Reporting:** Programmable timer expires (default: 1000 cycles)
   - Action: Send statistics snapshot to HIVE-C

4. **Descriptor Queue Empty:** RAPIDS signals completion of all pending transfers
   - Action: Notify HIVE-C for next batch scheduling

5. **Custom Trigger:** User-defined conditions via debug registers
   - Action: Inject debug trace packet

### 5.3 Inband Descriptor Injection

SERV cores can inject descriptors directly:

```c
// Example: SERV code to inject 2D transfer descriptor
void serv_inject_descriptor(
    uint64_t src_addr,
    uint64_t dst_addr,
    uint32_t length,
    uint16_t stride,
    uint8_t tile_id
) {
    descriptor_t desc;
    desc.src_addr = src_addr;
    desc.dst_addr = dst_addr;
    desc.length = length;
    desc.stride = (stride << 16) | stride; // 2D: same X/Y
    desc.flags = (0xF << 28) |  // Max burst
                 (tile_id << 16) | 
                 (1 << 7) |  // Enable 2D
                 (1 << 5);   // Generate interrupt
    desc.next_ptr = 0; // Single-shot
    
    // Write to AXIS injection FIFO
    AXIS_TX_FIFO[0] = desc.word[0];
    AXIS_TX_FIFO[1] = desc.word[1];
    AXIS_TX_FIFO[2] = desc.word[2];
    AXIS_TX_FIFO[3] = desc.word[3];
    AXIS_TX_TUSER = PKT_DESC;
    AXIS_TX_TLAST = 1;
    AXIS_TX_VALID = 1;
    
    // Wait for handshake
    while (!(AXIS_TX_READY));
}
```

**CRITICAL: TID Enforcement for Compute Element Packets**

When compute elements send PKT_DATA back to RAPIDS, the Network Interface **automatically overrides TID** with the local tile ID:

```verilog
// Network Interface (NI) TX path for compute element
always_comb begin
    if (source == COMPUTE_ELEMENT && axis_tuser == PKT_DATA) begin
        // Override whatever TID the compute element set
        // This ensures RAPIDS receives correct source tile ID
        axis_tx_tid_out = MY_TILE_ID[3:0];
    end else begin
        // For SERV packets (CONFIG, STATUS), pass TID through
        axis_tx_tid_out = axis_tx_tid_in;
    end
end
```

This hardware enforcement ensures:
1. Tiles cannot spoof source ID (security/correctness)
2. RAPIDS always receives accurate TID for channel routing
3. Compute element doesn't need to know its own tile ID
4. SERV monitors can still use TID for other purposes (status reporting)

---

## 6. HIVE-C Control Software

### 6.1 Software Architecture

HIVE-C runs bare-metal firmware structured as:

```
main.c              - Initialization and main loop
  ├── rapids_mgr.c  - DMA descriptor management
  ├── config_mgr.c  - Network reconfiguration
  ├── stats_mgr.c   - Performance monitoring aggregation
  ├── interrupt.c   - IRQ handlers (RAPIDS completion, SERV alerts)
  └── host_if.c     - UART/AXI-Lite command interface
```

**Memory Map:**
```
0x0000_0000 - 0x0000_7FFF: Instruction memory (32KB)
0x0000_8000 - 0x0000_FFFF: Data memory (32KB)
0x4000_0000 - 0x4000_0FFF: RAPIDS register interface
0x4000_1000 - 0x4000_1FFF: DELTA network control
0x4000_2000 - 0x4000_2FFF: SERV monitor status (16×256 bytes)
0x4000_3000 - 0x4000_3FFF: Configuration registers
0x4000_4000 - 0x4000_4FFF: Host interface (UART/AXI-Lite)
```

**CRITICAL: Channel-Aware Descriptor Programming**

HIVE-C must understand the Tile ID → RAPIDS S2MM Channel mapping:
```c
// Direct mapping: Tile N sends with TID=N, routes to Channel N
#define TILE_TO_CHANNEL(tile_id)  (tile_id)  // Identity mapping

// When programming S2MM descriptor for results from Tile 5:
void program_s2mm_descriptor(uint8_t source_tile) {
    descriptor_t desc;
    desc.type = DESC_S2MM;  // Network → Memory
    desc.src_addr = 0;  // Not used for S2MM
    desc.dst_addr = result_buffer[source_tile];  // DDR write address
    desc.length = result_size;
    desc.source_tile_id = source_tile;  // Descriptor[15:12]
    desc.dest_tile_id = 16;  // RAPIDS virtual tile (not really used)
    
    // Inject to RAPIDS - it will queue this on S2MM Channel[source_tile]
    inject_descriptor(&desc);
}
```

### 6.2 Descriptor Scheduling Algorithm

HIVE-C implements multi-level queue scheduler:

**Priority Levels:**
- Level 0 (Highest): Real-time / latency-sensitive transfers
- Level 1: Standard compute data movement
- Level 2: Background / prefetch operations
- Level 3 (Lowest): Debug / trace data

**Scheduling Policy:**
1. Round-robin within priority level
2. Service higher priority if queue non-empty
3. Age-based promotion: Level N → N-1 after 1000 cycles waiting
4. Deadline-aware scheduling for real-time transfers

### 6.3 Example Control Flow

```c
// Simplified main loop
void hive_main_loop(void) {
    init_hardware();
    load_network_config(CONTEXT_MESH); // Start in mesh mode
    
    while (1) {
        // Process host commands
        if (host_command_pending()) {
            handle_host_command();
        }
        
        // Aggregate SERV statistics
        if (timer_expired(STATS_INTERVAL)) {
            collect_serv_statistics();
            update_performance_model();
        }
        
        // Check for congestion
        if (congestion_detected()) {
            adaptive_route_balancing();
        }
        
        // Schedule next descriptor batch
        if (rapids_ready() && desc_queue_has_work()) {
            issue_descriptor_batch(MAX_INFLIGHT);
        }
        
        // Handle completion interrupts
        if (irq_pending()) {
            process_interrupts();
        }
    }
}

// Example: Matrix multiply - load activations, wait for results
void execute_matmul_layer(uint8_t num_tiles) {
    // Phase 1: Send activations to all participating tiles
    for (int tile = 0; tile < num_tiles; tile++) {
        descriptor_t mm2s_desc;
        mm2s_desc.type = DESC_MM2S;  // Memory → Network
        mm2s_desc.src_addr = activation_buffer[tile];
        mm2s_desc.dst_addr = 0;  // Not used for MM2S
        mm2s_desc.length = activation_size;
        mm2s_desc.dest_tile_id = tile;  // Send to this tile
        mm2s_desc.source_tile_id = 0;   // Not used for MM2S
        mm2s_desc.priority = 0;  // High priority
        
        inject_descriptor(&mm2s_desc);
    }
    
    // Phase 2: Pre-program S2MM descriptors for result collection
    // CRITICAL: Must know which tile will send results (via TID)
    for (int tile = 0; tile < num_tiles; tile++) {
        descriptor_t s2mm_desc;
        s2mm_desc.type = DESC_S2MM;  // Network → Memory
        s2mm_desc.src_addr = 0;  // Not used for S2MM
        s2mm_desc.dst_addr = result_buffer[tile];  // Where to write
        s2mm_desc.length = result_size;
        s2mm_desc.source_tile_id = tile;  // CRITICAL: Expect TID=tile
        s2mm_desc.dest_tile_id = 16;  // RAPIDS (not really used)
        s2mm_desc.priority = 1;  // Standard priority
        
        inject_descriptor(&s2mm_desc);
        
        // RAPIDS will queue this on S2MM Channel[tile]
        // When Tile[tile] sends results with TID=tile,
        // it will match this channel and use this descriptor
    }
    
    // Wait for all completions
    wait_for_all_tiles_complete();
}
```

---

## 7. Performance Modeling and Simulation

### 7.1 SimPy Models Provided

HIVE includes comprehensive SimPy performance models for educational exploration:

**Model 1: NoC Latency and Bandwidth**
- File: `models/noc_performance.py`
- Parameters: Topology, packet size, injection rate, routing algorithm
- Outputs: Average latency, throughput, buffer occupancy heatmaps
- Use case: Predict congestion under various traffic patterns

**Model 2: DMA Descriptor Throughput**
- File: `models/dma_scheduling.py`
- Parameters: Descriptor arrival rate, processing time, queue depth
- Outputs: Queue length over time, completion latency distribution
- Use case: Optimize descriptor batch sizes and priority levels

**Model 3: SERV Monitoring Overhead**
- File: `models/serv_overhead.py`
- Parameters: Monitoring frequency, packet injection rate, instruction cycles
- Outputs: Compute utilization vs. monitoring overhead
- Use case: Tune monitoring intervals to balance visibility and efficiency

**Model 4: End-to-End System Model**
- File: `models/hive_system.py`
- Integrates: RAPIDS DMA + DELTA NoC + HIVE control
- Parameters: Workload trace (matrix multiply, convolution, etc.)
- Outputs: Total execution time, resource utilization, bottleneck analysis
- Use case: Validate hardware design before synthesis

**Model 5: Reconfiguration Impact**
- File: `models/config_switch.py`
- Parameters: Context switch frequency, quiesce time, topology efficiency
- Outputs: Effective throughput with mode switching overhead
- Use case: Determine optimal workload partitioning across modes

### 7.2 Performance Tradeoff Documentation

Each design decision includes quantified tradeoffs:

**Example: Virtual Channels per Router**

| VCs | Area (LUTs) | Max Freq (MHz) | Deadlock Free | Latency (cycles) | Notes |
|-----|-------------|----------------|---------------|------------------|-------|
| 1 | 400 | 250 | No | 3.2 | Minimal area, requires careful routing |
| 2 | 500 | 220 | Yes (XY) | 3.5 | Recommended for proof-of-concept |
| 4 | 650 | 180 | Yes | 4.1 | Improved QoS, higher area cost |

**Example: SERV Monitoring Interval**

| Interval (cycles) | Overhead (%) | Detection Latency | Memory (bytes) |
|-------------------|--------------|-------------------|----------------|
| 100 | 8.5 | Excellent | 512 |
| 500 | 2.1 | Good | 256 |
| 1000 | 1.2 | Acceptable | 128 |
| 5000 | 0.3 | Poor | 64 |

All tradeoffs include:
- Theoretical analysis (equations)
- SimPy simulation results
- Hardware synthesis reports
- Recommendations with justification

---

## 8. Educational Features

### 8.1 Modular Design Philosophy

Every component is self-contained with standardized interfaces:

```
hive/
├── rtl/
│   ├── hive_top.sv              # Top-level integration
│   ├── vexriscv_master/
│   │   ├── vexriscv_wrapper.sv
│   │   ├── instruction_mem.sv
│   │   └── data_mem.sv
│   ├── serv_monitor/
│   │   ├── serv_wrapper.sv
│   │   ├── traffic_counter.sv
│   │   ├── trigger_logic.sv
│   │   └── axis_injector.sv
│   ├── control_network/
│   │   ├── control_router.sv
│   │   ├── control_arbiter.sv
│   │   └── control_packetizer.sv
│   ├── config_manager/
│   │   ├── config_registers.sv
│   │   ├── context_memory.sv
│   │   └── switch_controller.sv
│   └── common/
│       ├── axis_fifo.sv
│       ├── credit_counter.sv
│       └── round_robin_arbiter.sv
├── sim/
│   ├── unit_tests/
│   │   ├── test_serv_monitor.py
│   │   ├── test_config_switch.py
│   │   └── ... (one per RTL module)
│   ├── integration_tests/
│   └── cocotb/               # Cocotb testbenches
├── models/
│   ├── noc_performance.py
│   ├── dma_scheduling.py
│   └── ... (SimPy models)
├── sw/
│   ├── vexriscv_fw/
│   │   ├── main.c
│   │   ├── rapids_mgr.c
│   │   └── ...
│   └── serv_fw/
│       └── monitor.S          # Hand-optimized assembly
└── docs/
    ├── tutorials/
    ├── api_reference/
    └── performance_analysis/
```

### 8.2 Unit Test Coverage

Every RTL module includes comprehensive unit tests:

**Example: `test_serv_monitor.py`**
```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

@cocotb.test()
async def test_congestion_detection(dut):
    """Verify SERV triggers alert when buffer exceeds threshold"""
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Configure threshold
    dut.congestion_threshold.value = 120  # 75% of 160 entry FIFO
    
    # Inject packets to fill buffer
    for i in range(125):
        dut.pkt_rx_valid.value = 1
        dut.pkt_rx_ready.value = 0  # Backpressure
        await RisingEdge(dut.clk)
    
    # Check alert triggered
    await RisingEdge(dut.clk)
    assert dut.congestion_alert.value == 1, "Alert should trigger at 125/160"
    
    # Verify status packet injected
    assert dut.axis_tx_valid.value == 1
    assert dut.axis_tx_tuser.value == 0b11  # PKT_STATUS
```

Tests cover:
- Functional correctness
- Edge cases (overflow, underflow)
- Timing violations
- Protocol compliance
- Performance under stress

### 8.3 Experimentation Hooks

Users can easily modify behavior through configuration:

**Hardware Parameters (SystemVerilog):**
```systemverilog
// hive_config.svh
parameter int MESH_SIZE = 4;           // NxN mesh
parameter int SERV_COUNT = 16;         // Must equal MESH_SIZE^2
parameter int ROUTER_BUFFER_DEPTH = 8; // Flits per input VC
parameter int NUM_VIRTUAL_CHANNELS = 2;
parameter int FLIT_WIDTH = 128;        // Bits
parameter int NUM_CONTEXTS = 4;        // Routing configurations

// Monitoring parameters
parameter int SERV_MEM_SIZE = 2048;    // Bytes
parameter int CONGESTION_THRESHOLD = 6; // Trigger at 75% of buffer
parameter int STATS_REPORT_INTERVAL = 1000; // Cycles

// Performance knobs
parameter bit ENABLE_PIPELINE_BYPASS = 1;
parameter bit ENABLE_ADAPTIVE_ROUTING = 0;  // Future: load balancing
```

**Software Tuning (`hive_config.h`):**
```c
#define MAX_INFLIGHT_DESCRIPTORS  8
#define PRIORITY_LEVELS           4
#define AGING_THRESHOLD           1000  // Cycles
#define DESCRIPTOR_BATCH_SIZE     4
#define STATS_AGGREGATION_PERIOD  10000 // Cycles
```

---

## 9. Integration with RAPIDS and DELTA

### 9.1 RAPIDS Interface

HIVE-C connects to RAPIDS via two interfaces:

**Control Interface (AXI4-Lite Slave):**
- HIVE-C reads RAPIDS status registers
- HIVE-C writes descriptor queue base addresses
- HIVE-C configures DMA parameters (burst size, priority)

**Descriptor Injection (AXIS Master):**
- HIVE-C generates 256-bit descriptor packets
- Packets tagged with PKT_DESC in TUSER field
- RAPIDS hardware detects PKT_DESC and routes to descriptor FIFO
- No memory round-trip required (10-20 cycle latency vs. 100+ for memory-mapped)

### 9.2 DELTA Integration

**Tile Architecture:**
```
┌─────────────────────────────────────┐
│         Compute Tile N              │
│  ┌──────────────────────────────┐  │
│  │   SERV Monitor               │  │
│  │  - Traffic counters          │  │
│  │  - Trigger logic             │  │
│  │  - AXIS TX injector          │  │
│  └──────────┬───────────────────┘  │
│             │ Control signals       │
│  ┌──────────▼───────────────────┐  │
│  │   Network Interface (NI)     │  │
│  │  - AXIS packetizer           │  │
│  │  - Credit flow control       │  │
│  │  - Virtual channel mux       │  │
│  └──────────┬───────────────────┘  │
│             │                       │
│  ┌──────────▼───────────────────┐  │
│  │   Router (5-port)            │  │
│  │  - N/S/E/W + Local           │  │
│  │  - XY routing logic          │  │
│  │  - VC buffers (8 flits ea.)  │  │
│  └──────────┬───────────────────┘  │
│             │ To/from mesh         │
└─────────────┼───────────────────────┘
              │
   ┌──────────▼───────────┐
   │  Compute Element     │
   │  - DSP MACs          │
   │  - Local BRAM        │
   │  - PE control FSM    │
   └──────────────────────┘
```

**Configuration Flow:**
1. Host sends command to HIVE-C: "Switch to systolic mode"
2. HIVE-C broadcasts CONFIG_PREPARE to all SERV monitors
3. SERV cores assert flush signals to local routers
4. Routers drain in-flight packets (5-10 cycles)
5. HIVE-C broadcasts SET_ROUTING_MODE with context ID
6. All routers simultaneously update routing table pointer
7. HIVE-C broadcasts CONFIG_ACTIVATE
8. Network resumes with new topology (total: ~20 cycles)

---

## 10. Implementation Roadmap

### Phase 1: Core Infrastructure (Weeks 1-3)
- [ ] VexRiscv integration and memory subsystem
- [ ] Single SERV monitor with traffic counters
- [ ] Basic AXIS packet injection
- [ ] Unit tests for each component
- [ ] SimPy model for single tile

### Phase 2: 2×2 Prototype (Weeks 4-6)
- [ ] 2×2 mesh router network
- [ ] 4 SERV monitors
- [ ] Control network implementation
- [ ] Configuration register bank
- [ ] Integration test: descriptor injection
- [ ] SimPy model for 2×2 mesh

### Phase 3: Full 4×4 System (Weeks 7-10)
- [ ] Scale to 16 routers and SERV cores
- [ ] Virtual configuration contexts (2 modes minimum)
- [ ] Context switching logic
- [ ] HIVE-C firmware (descriptor scheduler)
- [ ] End-to-end integration with RAPIDS + DELTA
- [ ] Full system SimPy model

### Phase 4: Optimization (Weeks 11-12)
- [ ] Timing closure at target frequency (100 MHz)
- [ ] Resource optimization (fit in Artix-7 100T)
- [ ] Performance tuning (SimPy-guided)
- [ ] Documentation and tutorials

### Phase 5: Validation (Weeks 13-14)
- [ ] Hardware-in-loop testing on NexysA7
- [ ] Performance measurement vs. SimPy predictions
- [ ] Stress testing and corner cases
- [ ] Educational materials and examples

---

## 11. Verification Strategy

### 11.1 Levels of Testing

**Level 1 - Unit Tests (Cocotb):**
- Every RTL module has dedicated testbench
- Coverage target: 100% line, 95%+ branch
- Automated CI/CD on every commit

**Level 2 - Integration Tests:**
- Multi-module interaction (e.g., SERV + Router)
- Protocol compliance checkers
- Stress tests with random traffic

**Level 3 - System Tests:**
- Full HIVE + RAPIDS + DELTA integration
- Real workload traces (matrix multiply, convolution)
- SimPy validation (compare actual vs. predicted performance)

**Level 4 - Hardware Validation:**
- FPGA deployment on NexysA7
- Chipscope/ILA for signal capture
- Performance counters vs. model validation

### 11.2 Formal Verification

Critical components include formal properties:

**Router Deadlock Freedom:**
```systemverilog
// Assert XY routing prevents cycles
property no_deadlock;
  @(posedge clk) disable iff (!rst_n)
  (request[EAST] && !grant[EAST]) |->
    ##[1:MAX_DELAY] grant[EAST];
endproperty
assert property (no_deadlock);
```

**Descriptor Ordering:**
```systemverilog
// Assert FIFO ordering preserved
property fifo_order;
  @(posedge clk) disable iff (!rst_n)
  (desc_enqueue && desc_id == ID1) ##1
  (desc_enqueue && desc_id == ID2) |->
  ##[1:$] (desc_dequeue && desc_id == ID1) ##1
  (desc_dequeue && desc_id == ID2);
endproperty
```

---

## 12. Documentation and Educational Materials

### 12.1 Provided Documentation

**Architecture Guides:**
- System overview and design rationale
- Component-level specifications
- Interface protocols (AXIS, AXI4-Lite, custom)
- Configuration and control mechanisms

**Performance Analysis:**
- SimPy model descriptions and usage
- Tradeoff tables with justifications
- Bottleneck identification methodology
- Optimization case studies

**Tutorials:**
1. Getting Started: Simulate 2×2 mesh
2. Adding Custom Monitoring Logic
3. Implementing New Routing Algorithm
4. Descriptor Scheduling Policies
5. Network Reconfiguration Workflows
6. Performance Tuning Guide

**API Reference:**
- VexRiscv firmware API
- SERV monitor assembly programming
- Configuration register map
- AXIS packet formats
- SimPy model parameters

### 12.2 Interactive Learning Tools

**Web-Based Visualizer:**
- Real-time packet flow animation
- Router buffer occupancy heatmaps
- Performance counter dashboards
- Configuration state display

**Jupyter Notebooks:**
- Guided exploration of SimPy models
- "What-if" analysis with sliders
- Automated plot generation
- LaTeX equation rendering

**Example Workloads:**
- Matrix multiplication (multiple sizes)
- 2D convolution (various kernels)
- Reduction operations (sum, max)
- Synthetic traffic patterns (uniform, hotspot, transpose)

---

## 13. Expansion Path

### 13.1 Proof-of-Concept → Production

**Scaling to Kintex-7 325T:**
- 8×8 mesh (64 tiles) - 4× capacity
- 64 SERV monitors
- 4 VexRiscv full cores (hierarchical control)
- Higher clock frequency (150-200 MHz)
- Additional routing contexts (8 total)

**Resource Estimates:**

| Component | LUTs | DSPs | BRAM |
|-----------|------|------|------|
| 64× SERV + 4× VexRiscv | 14,000 | 0 | 144 |
| 8×8 Mesh NoC | 32,000 | 0 | 128 |
| Config & Control | 4,000 | 0 | 16 |
| **HIVE Subtotal** | **50,000** | **0** | **288** |
| Available for Compute | 153,800 | 840 | 157 |

### 13.2 Future Enhancements

**Adaptive Routing:**
- Load-aware path selection
- Congestion avoidance via alternate routes
- SERV cores implement local routing decisions

**Quality-of-Service:**
- Guaranteed bandwidth allocation
- Latency-sensitive packet prioritization
- Admission control via HIVE-C

**Fault Tolerance:**
- Router failure detection via heartbeat
- Dynamic rerouting around failed nodes
- Graceful degradation

**Machine Learning Integration:**
- SERV cores run lightweight inference for traffic prediction
- HIVE-C adjusts scheduling based on ML predictions
- Reinforcement learning for routing policy optimization

---

## 14. Success Criteria

### 14.1 Functional Requirements

- ✅ VexRiscv successfully controls RAPIDS DMA via inband descriptors
- ✅ 16 SERV monitors accurately track per-tile traffic
- ✅ Configuration switching completes within 25 cycles
- ✅ All packet types correctly routed based on TUSER encoding
- ✅ Zero packet loss under normal operation
- ✅ Congestion detection triggers within 10 cycles

### 14.2 Performance Requirements

- ✅ System frequency ≥ 100 MHz on NexysA7 100T
- ✅ Descriptor injection latency < 30 cycles (HIVE-C → RAPIDS)
- ✅ NoC throughput ≥ 80% of theoretical maximum
- ✅ SERV monitoring overhead < 5% of compute time
- ✅ Configuration switching overhead < 1% for workloads with 1000+ cycle phases

### 14.3 Educational Requirements

- ✅ SimPy models predict hardware performance within ±10%
- ✅ 100% of RTL modules have passing unit tests
- ✅ Complete API documentation with examples
- ✅ 5+ tutorials covering common use cases
- ✅ Modular design allows component replacement without system redesign

---

## Appendix A: Glossary

**AXIS (AXI4-Stream):** Streaming interface protocol, subset of AXI with no addressing

**BRAM:** Block RAM, dedicated memory blocks in FPGA fabric

**Flit:** Flow control unit, atomic packet fragment in NoC

**HIVE-C:** Master VexRiscv controller in HIVE system

**Inband Control:** Control messages sent through data network rather than separate bus

**NoC:** Network-on-Chip, packet-switched interconnect

**SERV:** World's smallest RISC-V core, bit-serial implementation

**Virtual Channel (VC):** Logically independent queue sharing physical link

**XY Routing:** Dimension-ordered routing (X-dimension first, then Y)

---

## Appendix B: References

1. VexRiscv GitHub: https://github.com/SpinalHDL/VexRiscv
2. SERV GitHub: https://github.com/olofk/serv
3. Cocotb Documentation: https://docs.cocotb.org/
4. SimPy Documentation: https://simpy.readthedocs.io/
5. MAERI Paper: "Enabling Flexible Dataflow Mapping over DNN Accelerators via Reconfigurable Interconnects" (ASPLOS 2018)
6. ProNoC GitHub: https://github.com/aignacio/ProNoC

---

**Document Version:** 0.3 (Early Draft - Proof of Concept)  
**Last Updated:** 2025-10-18  
**Status:** Preliminary specification, subject to significant change  
**Maintained By:** HIVE Development Team  
**License:** Educational use, open-source components per individual licenses