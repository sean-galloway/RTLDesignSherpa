# Bridge: AXI4 Full Crossbar Generator - Product Requirements Document

**Project:** Bridge
**Version:** 1.0
**Status:** 🟢 Specification Complete - Ready for Implementation
**Created:** 2025-10-18
**Last Updated:** 2025-10-18

---

## Executive Summary

**Bridge** is a Python-based AXI4 full crossbar generator that produces parameterized SystemVerilog RTL for connecting multiple AXI4 masters to multiple AXI4 slaves. The name follows the infrastructure theme - bridges connect different regions, enabling communication across divides, just like crossbars connect masters and slaves.

**Key Differentiator from Delta:**
- **Delta:** AXI-Stream crossbar (streaming data, single channel, simple routing)
- **Bridge:** AXI4 full crossbar (memory-mapped, 5 channels, burst support, ID-based routing)

**Target Use Case:** High-performance memory-mapped interconnects for multi-core processors, accelerators, and memory controllers.

---

## ⚠️ CRITICAL: RTL Regeneration Requirements

**ALL generated RTL files MUST be deleted and regenerated together whenever ANY generator code changes.**

**Why This Matters:**
- Generated RTL files may have interdependencies (bridges, wrappers, integrators)
- Generator code changes can create version mismatches between files
- Partial regeneration creates subtle incompatibilities that cause test failures
- Even "small innocuous" generator changes can have cascading effects

**The Rule:**
```bash
# ❌ WRONG - Partial regeneration
./bridge_generator.py --masters 5 --slaves 3 --output ../rtl/
# Only regenerates bridge_axi4_flat_5x3.sv
# Other files (wrappers, integrators) now mismatched!

# ✅ CORRECT - Full regeneration
rm ../rtl/bridge_*.sv                    # Delete ALL generated bridges
rm ../rtl/bridge_wrapper_*.sv            # Delete ALL generated wrappers
./regenerate_all_bridges.sh              # Regenerate everything together
```

**Generator Files That Trigger Full Regeneration:**
- `bridge_generator.py` - Main bridge generator
- `bridge_csv_generator.py` - CSV-based generator
- `bridge_address_arbiter.py` - Address decode logic
- `bridge_channel_router.py` - Channel routing logic
- `bridge_response_router.py` - Response routing logic
- `bridge_amba_integrator.py` - AMBA component integration
- `bridge_wrapper_generator.py` - Wrapper generation
- **Any** Python file in `projects/components/bridge/bin/`

**Symptoms of Version Mismatch:**
- Tests that previously passed now fail
- Simulation errors about missing signals
- Mismatched port widths or counts
- Address decode routing to wrong slaves

**Think of Generated RTL Like Compiled Code:**
When you update a compiler, you don't selectively recompile - you rebuild everything.
When you update a generator, you don't selectively regenerate - you regenerate everything.

---

## 1. Product Overview

### 1.1 Purpose

Bridge provides automated generation of AXI4 crossbar infrastructure with:
- **Python code generation** - Parameterized RTL generation (similar to APB/Delta)
- **Performance modeling** - Analytical + simulation validation
- **Flat topology** - Full M×N interconnect matrix
- **ID-based routing** - Out-of-order transaction support
- **Burst optimization** - Pipelined burst transfers

### 1.2 Target Audience

**Primary Users:**
- RTL designers building SoC interconnect
- System architects evaluating interconnect topologies
- Verification engineers needing crossbar testbenches
- Students learning AXI4 protocol and interconnects

**Educational Focus:**
- Demonstrates AXI4 protocol complexity
- Shows arbitration strategies for memory-mapped busses
- Teaches ID-based transaction tracking
- Illustrates burst optimization techniques

### 1.3 Success Criteria

**Functional:**
- [ ] Generates working AXI4 crossbar RTL
- [ ] Passes Verilator lint
- [ ] Supports 1-32 masters, 1-256 slaves
- [ ] Handles out-of-order completion via IDs
- [ ] Supports burst lengths 1-256 beats

**Performance:**
- [ ] Latency ≤ 3 cycles for single-beat transactions
- [ ] Throughput: All M×N paths can transfer concurrently
- [ ] Fmax ≥ 300 MHz on UltraScale+ FPGAs

**Quality:**
- [ ] Complete specifications (PRD) before code
- [ ] Performance models validate requirements
- [ ] All generated RTL Verilator verified
- [ ] Integration examples provided

---

## 2. Architecture Overview

### 2.1 AXI4 vs AXIS vs APB

| Feature | APB | AXI-Stream (Delta) | AXI4 (Bridge) |
|---------|-----|-------------------|---------------|
| **Protocol Type** | Simple register bus | Streaming data | Memory-mapped burst |
| **Channels** | 1 (address + data) | 1 (data stream) | 5 (AW, W, B, AR, R) |
| **Request Generation** | Address range decode | TDEST decode | Address range decode |
| **Arbitration** | Per-slave, per-cycle | Per-slave, packet-locked | Per-slave, per-address-phase |
| **Out-of-Order** | No (sequential) | No (streaming order) | Yes (ID-based) |
| **Burst Support** | No | Packet (via TLAST) | Yes (AWLEN/ARLEN) |
| **Complexity** | Low | Medium | **High** |
| **Latency** | 1-2 cycles | 2 cycles | 2-3 cycles |
| **Use Case** | Control registers | Data streaming | Memory-mapped I/O |

**Bridge Complexity Sources:**
1. **5 independent channels** requiring separate arbitration
2. **ID-based routing** for out-of-order completion
3. **Burst handling** with interleaving constraints
4. **Write response tracking** (match AW with B channel)
5. **Address decode + ID muxing** for response routing

### 2.2 Block Diagram

```
┌──────────────────────────────────────────────────────────────────────┐
│                          BRIDGE AXI4 CROSSBAR                        │
└──────────────────────────────────────────────────────────────────────┘

Masters (M)                                                    Slaves (S)
┌─────────┐                                                   ┌─────────┐
│ Master 0│ ─AW──┐                                      ┌─AW──│ Slave 0 │
│  (CPU)  │ ─W───┤                                      ├─W───│ (DDR)   │
│         │ ─B───┤                                      ├─B───│         │
│         │ ─AR──┤                                      ├─AR──│         │
│         │ ─R───┤                                      ├─R───│         │
└─────────┘      │                                      │     └─────────┘
                 │                                      │
┌─────────┐      │   ┌──────────────────────────┐      │     ┌─────────┐
│ Master 1│ ─────┼───│  Request Generation      │──────┼─────│ Slave 1 │
│  (GPU)  │      │   │  (Address Range Decode)  │      │     │ (SRAM)  │
└─────────┘      │   └──────────────────────────┘      │     └─────────┘
                 │             │                        │
┌─────────┐      │   ┌──────────────────────────┐      │     ┌─────────┐
│ Master 2│ ─────┼───│  Arbitration Matrix      │──────┼─────│ Slave 2 │
│  (DMA)  │      │   │  (5 separate arbiters    │      │     │ (PCIE)  │
└─────────┘      │   │   per slave: AW,W,B,AR,R)│      │     └─────────┘
                 │   └──────────────────────────┘      │
┌─────────┐      │             │                        │     ┌─────────┐
│ Master 3│ ─────┴───│  Data/Addr Multiplexing  │──────┴─────│ Slave 3 │
│ (Accel) │          │  (ID-based routing)      │            │ (Periph)│
└─────────┘          └──────────────────────────┘            └─────────┘
                               │
                     ┌──────────────────────────┐
                     │  Transaction Tracking    │
                     │  (ID tables for OoO)     │
                     └──────────────────────────┘
```

### 2.3 Key Components

**1. Request Generation**
- Address range decode for each slave
- Generates M×S request matrix per channel (AW, AR)
- Similar to APB but more complex (2 address channels)

**2. Per-Slave Arbitration**
- **5 separate arbiters per slave:**
  - AW channel arbiter (write address)
  - W channel arbiter (write data - locked to AW grant)
  - B channel arbiter (write response - routed by ID)
  - AR channel arbiter (read address)
  - R channel arbiter (read data - routed by ID)
- Round-robin with burst locking
- Separate read/write paths (no head-of-line blocking)

**3. Data Multiplexing**
- Mux master signals to selected slave
- ID-based response routing (B, R channels)
- Burst tracking (hold grant until xlast)

**4. Transaction Tracking**
- ID tables per slave for out-of-order support
- Track {Master ID, Transaction ID} → Master mapping
- Required for routing B/R channels back to correct master

**5. Optional Performance Counters**
- Transaction counts per master/slave
- Arbitration conflict counts
- Latency histograms

---

## 3. Functional Requirements

### 3.1 AXI4 Protocol Compliance

**FR-1: Full AXI4 Protocol Support**
- Support all 5 AXI4 channels: AW, W, B, AR, R
- Comply with AMBA AXI4 specification (ARM IHI 0022)
- Support burst lengths: 1-256 beats (AWLEN/ARLEN = 0-255)
- Support burst types: INCR, WRAP, FIXED
- Support burst sizes: 1-128 bytes (AWSIZE/ARSIZE = 0-7)

**FR-2: Out-of-Order Transaction Support**
- Route responses via ID matching
- Maintain transaction ID integrity (AWID → BID, ARID → RID)
- Support configurable ID width (1-16 bits)
- Track up to 2^ID_WIDTH outstanding transactions per slave

**FR-3: Atomic Operations**
- Support exclusive access (AWLOCK/ARLOCK)
- Track exclusive monitor per slave
- Generate BRESP/RRESP errors for failed exclusives

### 3.2 Address Decoding

**FR-4: Configurable Address Map**
- Support M masters × S slaves
- Each slave has base address and size
- Non-overlapping address ranges (verified at generation)
- Default slave for unmapped addresses (optional)

**FR-5: Address Range Configuration**
```python
# Example address map
address_map = {
    0: {'base': 0x00000000, 'size': 0x40000000, 'name': 'DDR'},      # 1GB
    1: {'base': 0x40000000, 'size': 0x00100000, 'name': 'SRAM'},     # 1MB
    2: {'base': 0x50000000, 'size': 0x01000000, 'name': 'PCIE'},     # 16MB
    3: {'base': 0x60000000, 'size': 0x00010000, 'name': 'Peripherals'} # 64KB
}
```

### 3.3 Arbitration Strategy

**FR-6: Round-Robin Arbitration**
- Fair bandwidth allocation (no starvation)
- Separate arbiters for AW and AR channels
- Burst locking: Grant held until xlast (WLAST/RLAST)
- Configurable arbitration policy (round-robin default)

**FR-7: Read/Write Independence**
- Separate read and write paths
- No head-of-line blocking between read/write
- Concurrent read and write to same slave (if slave supports)

### 3.4 Burst Handling

**FR-8: Burst Optimization**
- Pipelined burst transfers (overlap address and data)
- No artificial burst splitting
- Full AXI4 burst protocol support

**FR-9: Interleaving Constraints**
- W channel locked to AW grant master
- R channel routed by transaction ID
- Support ID-based interleaving (slave-dependent)

---

## 4. Non-Functional Requirements

### 4.1 Performance

**NFR-1: Latency**
- **Single-beat read:** ≤ 3 cycles (address decode + arbitration + mux)
- **Single-beat write:** ≤ 3 cycles (address decode + arbitration + mux)
- **Burst transfer:** No additional latency per beat (pipelined)

**NFR-2: Throughput**
- **Concurrent transfers:** All M×S paths can transfer simultaneously
- **Burst efficiency:** Line-rate data transfer after address phase
- **No artificial stalls:** Crossbar adds no wait states beyond arbitration

**NFR-3: Fmax**
- **Target:** 300-400 MHz on Xilinx UltraScale+
- **Registered outputs:** All slave outputs registered for timing closure
- **Pipelineable:** Optional pipeline stages for >400 MHz

### 4.2 Resource Usage (Estimated)

**M = 4 masters, S = 4 slaves, DATA_WIDTH = 512, ADDR_WIDTH = 64, ID_WIDTH = 4:**

| Resource | Flat Crossbar | Notes |
|----------|---------------|-------|
| **LUTs** | ~2,500 | Address decode + arbiters + mux |
| **FFs** | ~3,000 | Registered outputs + ID tables |
| **BRAM** | 0 | Distributed RAM for small ID tables |
| **DSP** | 0 | No arithmetic operations |

**Scaling:** ~150 LUTs per M×S connection

### 4.3 Quality Requirements

**NFR-4: Code Generation Quality**
- Lint-clean SystemVerilog (Verilator)
- Synthesizable (Vivado, Yosys, Design Compiler)
- No vendor-specific primitives (technology-agnostic)
- Clear structure (commented, readable)

**NFR-5: Verification**
- CocoTB testbench framework
- Transaction-level verification
- Out-of-order test scenarios
- Burst interleaving tests
- >95% functional coverage

---

## 5. Interface Specifications

### 5.1 AXI4 Master Interfaces (M × 5 channels)

**Write Address Channel (AW):**
```systemverilog
input  logic [ADDR_WIDTH-1:0]   s_axi_awaddr  [NUM_MASTERS];
input  logic [ID_WIDTH-1:0]     s_axi_awid    [NUM_MASTERS];
input  logic [7:0]              s_axi_awlen   [NUM_MASTERS];  // Burst length-1
input  logic [2:0]              s_axi_awsize  [NUM_MASTERS];  // Burst size
input  logic [1:0]              s_axi_awburst [NUM_MASTERS];  // INCR/WRAP/FIXED
input  logic                    s_axi_awlock  [NUM_MASTERS];  // Exclusive access
input  logic [3:0]              s_axi_awcache [NUM_MASTERS];  // Cache attributes
input  logic [2:0]              s_axi_awprot  [NUM_MASTERS];  // Protection type
input  logic                    s_axi_awvalid [NUM_MASTERS];
output logic                    s_axi_awready [NUM_MASTERS];
```

**Write Data Channel (W):**
```systemverilog
input  logic [DATA_WIDTH-1:0]   s_axi_wdata  [NUM_MASTERS];
input  logic [DATA_WIDTH/8-1:0] s_axi_wstrb  [NUM_MASTERS];  // Byte strobes
input  logic                    s_axi_wlast  [NUM_MASTERS];  // Last beat
input  logic                    s_axi_wvalid [NUM_MASTERS];
output logic                    s_axi_wready [NUM_MASTERS];
```

**Write Response Channel (B):**
```systemverilog
output logic [ID_WIDTH-1:0]     s_axi_bid    [NUM_MASTERS];
output logic [1:0]              s_axi_bresp  [NUM_MASTERS];  // OKAY/EXOKAY/SLVERR/DECERR
output logic                    s_axi_bvalid [NUM_MASTERS];
input  logic                    s_axi_bready [NUM_MASTERS];
```

**Read Address Channel (AR):**
```systemverilog
input  logic [ADDR_WIDTH-1:0]   s_axi_araddr  [NUM_MASTERS];
input  logic [ID_WIDTH-1:0]     s_axi_arid    [NUM_MASTERS];
input  logic [7:0]              s_axi_arlen   [NUM_MASTERS];
input  logic [2:0]              s_axi_arsize  [NUM_MASTERS];
input  logic [1:0]              s_axi_arburst [NUM_MASTERS];
input  logic                    s_axi_arlock  [NUM_MASTERS];
input  logic [3:0]              s_axi_arcache [NUM_MASTERS];
input  logic [2:0]              s_axi_arprot  [NUM_MASTERS];
input  logic                    s_axi_arvalid [NUM_MASTERS];
output logic                    s_axi_arready [NUM_MASTERS];
```

**Read Data Channel (R):**
```systemverilog
output logic [DATA_WIDTH-1:0]   s_axi_rdata  [NUM_MASTERS];
output logic [ID_WIDTH-1:0]     s_axi_rid    [NUM_MASTERS];
output logic [1:0]              s_axi_rresp  [NUM_MASTERS];
output logic                    s_axi_rlast  [NUM_MASTERS];
output logic                    s_axi_rvalid [NUM_MASTERS];
input  logic                    s_axi_rready [NUM_MASTERS];
```

### 5.2 AXI4 Slave Interfaces (S × 5 channels)

Mirror of master interfaces, with M → S direction reversed.

### 5.3 Configuration Parameters

```systemverilog
parameter int NUM_MASTERS   = 4;          // Number of master interfaces
parameter int NUM_SLAVES    = 4;          // Number of slave interfaces
parameter int DATA_WIDTH    = 512;        // Data bus width (bits)
parameter int ADDR_WIDTH    = 64;         // Address bus width (bits)
parameter int ID_WIDTH      = 4;          // Transaction ID width (bits)
parameter int MAX_BURST_LEN = 256;        // Maximum burst length (beats)
parameter bit PIPELINE_OUTPUTS = 1;       // Register slave outputs
parameter bit ENABLE_COUNTERS  = 1;       // Performance counters
```

---

## 6. Performance Modeling

### 6.1 Analytical Model

**Latency Components (Flat Crossbar):**

```
Single-Beat Read Latency:
  1. Address Decode:      0 cycles (combinatorial)
  2. Arbitration:         1 cycle  (AR arbiter decision)
  3. Address Mux:         0 cycles (combinatorial)
  4. Slave Access:        (slave-dependent, not crossbar)
  5. Response Mux:        1 cycle  (R channel ID lookup + mux)
  6. Output Register:     1 cycle  (optional, for timing closure)

  Total (no pipeline):    2 cycles
  Total (pipelined):      3 cycles
```

**Burst Transfer Throughput:**
```
After address phase completes, data transfer is line-rate:
  - W channel: 1 beat/cycle (locked to AW grant)
  - R channel: 1 beat/cycle (ID-routed from slave)

Example: 256-beat burst
  Address phase:  2-3 cycles (one-time)
  Data phase:     256 cycles (line-rate)
  Total:          258-259 cycles
  Efficiency:     98.8%
```

**Concurrent Throughput:**
```
Maximum concurrent transfers (4×4 crossbar):
  - Read:  4 concurrent (one per master-slave pair)
  - Write: 4 concurrent (one per master-slave pair)
  - Total: 8 concurrent read+write (separate paths)

Throughput @ 100 MHz, 512-bit data:
  Per path:   100 MHz × 512 bits = 51.2 Gbps
  Total:      8 paths × 51.2 Gbps = 409.6 Gbps theoretical
```

### 6.2 Resource Scaling

**LUT Usage Formula (empirical):**
```
LUTs ≈ 500 (base) + 150 × M × S + 20 × ID_TABLE_DEPTH
```

**Example (4×4 crossbar, ID_WIDTH=4, ID_TABLE_DEPTH=16 per slave):**
```
LUTs ≈ 500 + 150 × 16 + 20 × 16 × 4
     ≈ 500 + 2,400 + 1,280
     ≈ 4,180 LUTs
```

### 6.3 Comparison with Other Crossbars

| Crossbar Type | Latency | Throughput | Complexity | Use Case |
|---------------|---------|------------|------------|----------|
| **APB** | 1-2 cycles | Low (serialized) | Low | Control registers |
| **AXI-Stream (Delta)** | 2 cycles | High (streaming) | Medium | Data streaming |
| **AXI4 (Bridge)** | 2-3 cycles | High (burst) | **High** | Memory-mapped I/O |
| **AXI4 + Slices** | 4-6 cycles | High (burst) | Very High | >400 MHz designs |

**Bridge Sweet Spot:** High-performance memory-mapped interconnects where out-of-order and burst efficiency are critical.

---

## 7. Generator Architecture

### 7.1 Python Generator Structure

```python
class BridgeGenerator:
    """AXI4 crossbar RTL generator"""

    def __init__(self, config):
        self.num_masters = config.num_masters
        self.num_slaves = config.num_slaves
        self.data_width = config.data_width
        self.addr_width = config.addr_width
        self.id_width = config.id_width
        self.address_map = config.address_map

    def generate_address_decode(self) -> str:
        """Generate address range decode logic"""
        # For each master × slave, check if address in range
        # More complex than AXIS (uses address), simpler than full decode

    def generate_aw_arbiter(self, slave_idx) -> str:
        """Generate write address channel arbiter for one slave"""
        # Round-robin arbiter
        # Grants locked until corresponding B response completes

    def generate_ar_arbiter(self, slave_idx) -> str:
        """Generate read address channel arbiter for one slave"""
        # Round-robin arbiter
        # Grants locked until corresponding R response completes (RLAST)

    def generate_w_channel_mux(self, slave_idx) -> str:
        """Generate write data channel multiplexer"""
        # W channel follows AW grant (locked until WLAST)

    def generate_b_channel_demux(self, slave_idx) -> str:
        """Generate write response channel demultiplexer"""
        # Route by ID: lookup master from {slave_idx, BID}

    def generate_r_channel_demux(self, slave_idx) -> str:
        """Generate read data channel demultiplexer"""
        # Route by ID: lookup master from {slave_idx, RID}

    def generate_id_table(self, slave_idx) -> str:
        """Generate transaction ID tracking table"""
        # Maps {slave, transaction_id} → master_id
        # Indexed on AW/AR grant, looked up on B/R response

    def generate_crossbar(self) -> str:
        """Generate complete crossbar module"""
        # Instantiate all arbiters, muxes, demuxes, ID tables
```

### 7.2 Address Map Configuration

**Python Configuration:**
```python
bridge_config = {
    'num_masters': 4,
    'num_slaves': 4,
    'data_width': 512,
    'addr_width': 64,
    'id_width': 4,
    'address_map': {
        0: {'base': 0x00000000, 'size': 0x40000000, 'name': 'DDR'},
        1: {'base': 0x40000000, 'size': 0x00100000, 'name': 'SRAM'},
        2: {'base': 0x50000000, 'size': 0x01000000, 'name': 'PCIE'},
        3: {'base': 0x60000000, 'size': 0x00010000, 'name': 'Peripherals'}
    },
    'pipeline_outputs': True,
    'enable_counters': True
}
```

**Generated Address Decode:**
```systemverilog
// Address decode for each master
always_comb begin
    for (int s = 0; s < NUM_SLAVES; s++)
        aw_request_matrix[s] = '0;

    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (s_axi_awvalid[m]) begin
            // Slave 0: DDR (0x00000000 - 0x3FFFFFFF)
            if (s_axi_awaddr[m] >= 64'h00000000 &&
                s_axi_awaddr[m] < 64'h40000000)
                aw_request_matrix[0][m] = 1'b1;

            // Slave 1: SRAM (0x40000000 - 0x400FFFFF)
            if (s_axi_awaddr[m] >= 64'h40000000 &&
                s_axi_awaddr[m] < 64'h40100000)
                aw_request_matrix[1][m] = 1'b1;

            // ... slaves 2-3 ...
        end
    end
end
```

---

## 8. Comparison with APB and Delta

### 8.1 Code Reuse from APB Generator

**Similar Components (~70% reuse):**
- Address range decode logic (same pattern, different signals)
- Round-robin arbiter (same algorithm)
- Data multiplexing pattern (same approach)
- Backpressure handling (similar to PREADY)

**New Components for Bridge:**
- **5× the arbiters** (AW, W, B, AR, R instead of single channel)
- **ID-based routing** (B and R channel demuxing)
- **Transaction tracking** (ID tables for out-of-order)
- **Burst handling** (grant locking until xlast)

**Migration Effort from APB:**
- ~120 minutes (vs ~75 min for AXIS, due to higher complexity)
- Most time: ID table logic and response demuxing

### 8.2 Code Reuse from Delta Generator

**Similar Components (~60% reuse):**
- Python generation framework
- Command-line interface
- Performance modeling structure
- Arbitration pattern (round-robin with locking)

**Key Differences:**
- **5 channels** vs 1 channel (Delta only has TDATA/TVALID/TREADY/TLAST)
- **ID-based routing** vs TDEST-based routing
- **Address decode** vs TDEST decode (Bridge more complex)
- **Transaction tracking** vs packet atomicity (different mechanisms)

### 8.3 Complexity Comparison

| Metric | APB Crossbar | Delta (AXIS) | Bridge (AXI4) |
|--------|--------------|--------------|---------------|
| **Channels to arbitrate** | 1 | 1 | 5 ★ |
| **Request generation** | Address ranges | TDEST decode | Address ranges |
| **Response routing** | Grant-based | Grant-based | ID-based ★ |
| **Burst support** | No | Packet (TLAST) | Yes (AWLEN/ARLEN) ★ |
| **Out-of-order** | No | No | Yes (ID tables) ★ |
| **Transaction tracking** | No | No | Yes ★ |
| **Lines of Python** | ~500 | ~697 | **~900** (est.) |
| **Lines of generated SV** | ~200 (4×4) | ~250 (4×4) | **~400** (4×4) (est.) |

★ = Additional complexity in Bridge

---

## 9. Use Cases

### 9.1 Multi-Core Processor Interconnect

**Scenario:** 4 CPU cores + GPU accessing DDR + SRAM + Peripherals

```
Configuration:
  Masters:  5 (4 CPUs, 1 GPU)
  Slaves:   3 (DDR, SRAM, Peripherals)
  Data:     512-bit (cache line width)
  Address:  64-bit (large memory space)
  ID:       4-bit (up to 16 outstanding per master)
```

**Benefits:**
- Concurrent access to all slaves
- Out-of-order completion for high-performance CPUs
- Burst transfers for cache line fills
- Separate read/write paths (no head-of-line blocking)

### 9.2 DMA + Accelerator System

**Scenario:** DMA engine + 4 accelerators accessing shared memory

```
Configuration:
  Masters:  5 (1 DMA, 4 accelerators)
  Slaves:   2 (DDR, Control registers)
  Data:     512-bit (high-bandwidth DMA)
  Address:  32-bit (limited address space)
  ID:       2-bit (simple ID space)
```

**Benefits:**
- High-bandwidth memory access for DMA
- Fair arbitration prevents accelerator starvation
- Control register access doesn't block data transfers

### 9.3 FPGA System Integration

**Scenario:** MicroBlaze CPU + custom accelerators + memory controllers

```
Configuration:
  Masters:  8 (1 CPU, 7 accelerators)
  Slaves:   4 (DDR, BRAM, AXI GPIO, AXI DMA)
  Data:     128-bit (AXI4 standard width)
  Address:  32-bit (standard FPGA address space)
  ID:       4-bit (moderate outstanding transactions)
```

**Benefits:**
- Standard AXI4 interfaces (Xilinx IP compatibility)
- Scalable to many masters/slaves
- Performance counters for profiling

---

## 10. Testing Strategy

### 10.1 FUB (Functional Unit Block) Tests

**Address Decode Tests:**
- Verify all address ranges correctly decoded
- Test boundary conditions (base, base+size-1)
- Test unmapped addresses (error response)

**Arbiter Tests:**
- Round-robin fairness (all masters get turns)
- Burst locking (grant held until xlast)
- Starvation prevention

**ID Table Tests:**
- Correct ID → master mapping
- Out-of-order transaction handling
- Table full condition

**Mux/Demux Tests:**
- Data integrity through crossbar
- Response routing to correct master
- Concurrent transfers don't interfere

### 10.2 Integration Tests

**Single-Master, Single-Slave:**
- Basic read/write transactions
- Burst transfers (various lengths)
- Out-of-order completions

**Multi-Master, Single-Slave:**
- Arbitration correctness
- Fairness verification
- Burst interleaving (if supported)

**Multi-Master, Multi-Slave:**
- Concurrent transfers
- No crosstalk between paths
- Full M×S matrix coverage

**Stress Tests:**
- All masters active simultaneously
- Maximum burst lengths
- Full ID space utilization
- Back-to-back bursts

### 10.3 Performance Validation

**Latency Measurement:**
- Single-beat read: measure actual vs analytical
- Single-beat write: measure actual vs analytical
- Compare with specification (≤3 cycles)

**Throughput Measurement:**
- Burst transfer efficiency (should be ~98%)
- Concurrent path throughput (should be line-rate × M×S)
- Compare with theoretical maximum

**Resource Validation:**
- Synthesize for Xilinx UltraScale+
- Compare LUT/FF usage with estimates
- Verify Fmax ≥ 300 MHz

---

## 11. Documentation Plan

### 11.1 Specifications (Before Code)

- [x] **PRD.md** - This document (complete requirements)
- [ ] **README.md** - User guide with quick start
- [ ] **BRIDGE_VS_APB_GENERATOR.md** - Migration guide from APB
- [ ] **BRIDGE_VS_DELTA_GENERATOR.md** - Comparison with Delta
- [ ] **AXI4_PROTOCOL_GUIDE.md** - AXI4 primer for students

### 11.2 Performance Analysis (Before Implementation)

- [ ] **bin/bridge_performance_model.py** - Analytical model
  - Latency calculations (single-beat, burst)
  - Throughput estimates (concurrent paths)
  - Resource estimates (LUT/FF scaling)
- [ ] **bin/bridge_simulator.py** - Discrete event simulation (optional)
  - Cycle-accurate modeling
  - Traffic pattern support
  - Validation against RTL

### 11.3 Code Generation

- [ ] **bin/bridge_generator.py** - Main RTL generator
  - Command-line interface
  - Address map configuration
  - Generated RTL output

### 11.4 Verification

- [ ] **dv/tests/** - CocoTB testbenches
  - FUB tests (individual blocks)
  - Integration tests (multi-block)
  - Stress tests (corner cases)

---

## 12. Success Metrics

### 12.1 Functional Completeness

- [ ] Generates working AXI4 crossbar RTL
- [ ] Passes all CocoTB tests
- [ ] Verilator lint clean
- [ ] Xilinx Vivado synthesis clean

### 12.2 Performance Targets

- [ ] Latency ≤ 3 cycles (measured in simulation)
- [ ] Throughput = line-rate × M×S paths (measured)
- [ ] Fmax ≥ 300 MHz (post-synthesis)

### 12.3 Educational Value

- [ ] Complete specifications demonstrating rigor
- [ ] Performance models validate requirements
- [ ] Clear code structure (readable generated RTL)
- [ ] Integration examples provided

### 12.4 Reusability

- [ ] ~70% code reuse from APB generator (measured by LOC)
- [ ] Similar patterns to Delta generator
- [ ] Can be extended (weighted arbitration, QoS, etc.)

---

## 12. Attribution and Contribution Guidelines

### 12.1 Git Commit Attribution

When creating git commits for Bridge documentation or implementation:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** Bridge documentation and organization receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

## 12.2 PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/bridge/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/bridge/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the bridge_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## 13. Future Enhancements

### 13.1 Short-Term (Post-Initial Release)

- [ ] **Optional pipeline stages** - For Fmax >400 MHz
- [ ] **Weighted arbitration** - QoS support
- [ ] **Default slave** - Unmapped address handling
- [ ] **Exclusive monitor** - Full atomic operation support

### 13.2 Long-Term

- [ ] **Tree topology** - Hierarchical crossbar (like Delta)
- [ ] **AXI4-Lite variant** - Simplified for control registers
- [ ] **ACE support** - Coherent cache interconnect
- [ ] **GUI configurator** - Visual address map setup

---

## 14. Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| **ID table complexity** | Medium | High | Start with small ID_WIDTH (2-4), test thoroughly |
| **Out-of-order corner cases** | High | High | Extensive CocoTB tests with random delays |
| **Fmax below target** | Low | Medium | Optional pipeline stages for timing closure |
| **Resource usage exceeds** | Low | Low | Empirical formulas guide expectations |
| **Burst interleaving bugs** | Medium | High | Separate test suite for burst scenarios |

---

## 15. Project Timeline (Estimated)

**Week 1: Specifications and Models**
- [x] Day 1-2: PRD.md (complete)
- [ ] Day 3-4: Performance modeling (analytical)
- [ ] Day 5-7: README.md, migration guides

**Week 2-3: Core Implementation**
- [ ] Day 1-3: Address decode + arbiter generation
- [ ] Day 4-5: Data mux/demux generation
- [ ] Day 6-8: ID table generation
- [ ] Day 9-10: Integration and testing

**Week 4: Verification and Examples**
- [ ] Day 1-5: CocoTB testbenches
- [ ] Day 6-7: Integration examples

---

## 16. References

**AXI4 Specifications:**
- ARM IHI 0022 - AMBA AXI and ACE Protocol Specification
- Xilinx UG1037 - Vivado AXI Reference Guide

**Related Projects:**
- **APB Crossbar** - Simple register bus crossbar (existing)
- **Delta (AXIS Crossbar)** - Streaming data crossbar (projects/components/delta/)
- **RAPIDS** - DMA engine with AXI4 masters (rtl/miop/)

**Tools:**
- Verilator - RTL linting and simulation
- CocoTB - Python-based verification
- Xilinx Vivado - FPGA synthesis

---

## 17. Glossary

- **AXI4:** Advanced eXtensible Interface version 4 (AMBA standard)
- **Burst:** Multi-beat transaction (AWLEN/ARLEN > 0)
- **Crossbar:** Full M×N interconnect matrix
- **ID:** Transaction identifier for out-of-order support
- **Out-of-order:** Responses can return in different order than requests
- **xlast:** WLAST (write) or RLAST (read) - last beat indicator

---

**Version:** 1.0
**Status:** ✅ Specification Complete - Ready for Implementation
**Next Steps:** Create performance models, then implement generator

**Project Bridge - Connecting masters and slaves across the divide 🌉**
