# Product Requirements Document (PRD)
## STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory

**Version:** 1.0
**Date:** 2025-10-17
**Status:** Initial Design - Under Review
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The **STREAM** (Scatter-gather Transfer Rapid Engine for AXI Memory) is a simplified DMA-style accelerator designed for efficient memory-to-memory data movement with descriptor-based scatter-gather support. STREAM serves as a beginner-friendly tutorial demonstrating descriptor-based DMA engine design patterns while maintaining production-quality RTL practices.

### 1.1 Quick Stats

- **Modules:** ~8-10 SystemVerilog files (estimated)
- **Channels:** Maximum 8 independent channels
- **Interfaces:** APB (config), AXI4 (descriptor fetch + data read/write), MonBus (monitoring)
- **Architecture:** Simplified from RAPIDS - pure memory-to-memory
- **Tutorial Focus:** Aligned addresses only, straightforward data flow
- **Status:** Initial design phase

### 1.2 Project Goals

- **Primary:** Educational DMA engine demonstrating scatter-gather descriptor chains
- **Secondary:** Production-quality RTL suitable for FPGA/ASIC implementation
- **Tertiary:** Foundation for understanding more complex DMA architectures (e.g., RAPIDS)

---

## 2. Key Design Principles

### 2.1 Simplifications from RAPIDS

STREAM is intentionally simplified for tutorial purposes:

| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Network Interfaces** | Yes (Network master/slave) | ❌ No (pure memory-to-memory) |
| **Address Alignment** | Complex fixup logic | ✅ **Aligned addresses only** |
| **Credit Management** | Exponential encoding | ✅ Simple transaction limits |
| **Control Engines** | Control read/write engines | ❌ No (direct APB config) |
| **Descriptor Length** | Chunks (4-byte) | ✅ **Beats** (data width) |
| **Program Engine** | Complex alignment FSM | ✅ Simplified coordination |

### 2.2 Tutorial-Friendly Features

- **Aligned Addresses:** Source and destination addresses must be aligned to data width
- **Length in Beats:** Descriptor length specified in data beats (not bytes/chunks)
- **Single APB Write:** One APB register write kicks off entire descriptor chain
- **No Circular Buffers:** Chained descriptors with explicit termination
- **Parameterized Engines:** Multiple AXI engine versions (compile-time selection)

---

## 3. Architecture Overview

### 3.1 Top-Level Block Diagram

```
STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory)
├── APB Config Slave
│   └── Channel registers (8 channels, kick-off via write)
│
├── Descriptor Fetch
│   └── AXI Master (Read) - Fetch descriptors from memory
│
├── Scheduler Group (shared across all channels)
│   ├── Descriptor Engine   (FIFO, parsing - FROM RAPIDS)
│   ├── Scheduler           (Simplified FSM coordination)
│   └── Channel Arbitration (8 independent channels)
│
├── Data Path (shared resources)
│   ├── AXI Master (Read)  - Parameterized data width
│   ├── Simple SRAM        - Dual-port buffer (FROM RAPIDS)
│   └── AXI Master (Write) - Parameterized data width
│
└── MonBus Reporter
    └── MonBus Master - 64-bit monitoring packets
```

### 3.2 Data Flow

**Descriptor-Based Transfer Sequence:**

```
1. Software writes to APB channel register
   ↓
2. Descriptor fetch via AXI descriptor master
   ↓
3. Descriptor Engine parses descriptor fields
   ↓
4. Scheduler coordinates data transfer:
   a. AXI Read Engine fetches source data → SRAM buffer
   b. AXI Write Engine writes SRAM → destination
   ↓
5. Check for chained descriptor (next_descriptor_ptr != 0)
   ↓ (if chained)
6. Fetch next descriptor, repeat from step 3
   ↓ (if last)
7. Generate MonBus completion packet
```

**Channel Independence:**
- 8 channels operate independently
- All channels share: SRAM, AXI data masters, descriptor fetch master
- Arbitration required for shared resources

---

## 4. Interfaces

### 4.1 External Interfaces

| Interface | Type | Width | Purpose | Notes |
|-----------|------|-------|---------|-------|
| **APB Slave** | Slave | 32-bit | Configuration, channel kick-off | Write to channel register starts transfer |
| **AXI Master (Descriptor)** | Master | 256-bit | Fetch descriptors from memory | Dedicated descriptor fetch path |
| **AXI Master (Data Read)** | Master | Parameterizable | Read source data | Multiple engine versions (compile-time) |
| **AXI Master (Data Write)** | Master | Parameterizable | Write destination data | Multiple engine versions (compile-time) |
| **MonBus Master** | Master | 64-bit | Monitor packet output | Standard AMBA format |

### 4.2 Descriptor Format

**256-bit Descriptor Structure:**

| Bits | Field | Description |
|------|-------|-------------|
| [63:0] | `src_addr` | Source address (64-bit, must be aligned to data width) |
| [127:64] | `dst_addr` | Destination address (64-bit, must be aligned to data width) |
| [159:128] | `length` | Transfer length in **BEATS** (not bytes!) |
| [191:160] | `next_descriptor_ptr` | Address of next descriptor (0 = last in chain) |
| [192] | `valid` | Descriptor is valid |
| [193] | `interrupt` | Generate interrupt on completion |
| [194] | `last` | Last descriptor in chain (explicit flag) |
| [195] | `error` | Error status (used for reporting) |
| [199:196] | `channel_id` | Channel ID (0-7) |
| [207:200] | `priority` | Transfer priority (for arbitration) |
| [255:208] | `reserved` | Reserved for future use |

**Key Descriptor Features:**
- ✅ **Chained descriptors:** `next_descriptor_ptr` links to next descriptor
- ❌ **No circular buffers:** Explicit termination (last flag or ptr=0)
- ✅ **Length in beats:** Simplified for tutorial (no byte/chunk conversion)
- ✅ **Aligned addresses:** Tutorial constraint (performance hidden for now)

---

## 5. Key Components

### 5.1 Descriptor Engine

**Source:** Direct copy from RAPIDS `descriptor_engine.sv`

**Purpose:**
- FIFO-based descriptor storage
- APB interface for descriptor writes
- RDA (Read Descriptor Array) interface for AXI descriptor fetch
- Descriptor parsing and distribution

**Why Reuse:**
- Proven, tested design from RAPIDS
- 100% test pass rate (14/14 tests)
- Comprehensive APB and RDA path coverage

**Adaptation:**
- Update package import (`stream_imports.svh` instead of `rapids_imports.svh`)
- Minimal changes to core logic

### 5.2 Scheduler (Simplified from RAPIDS)

**Purpose:**
- Coordinate descriptor-to-data-transfer flow
- Manage 8 independent channels
- Arbitrate shared resources (SRAM, AXI masters)

**FSM States:**
```systemverilog
typedef enum logic [7:0] {
    SCHED_IDLE              = 8'b00000001,  // Idle, waiting for channel activation
    SCHED_FETCH_DESCRIPTOR  = 8'b00000010,  // Fetch descriptor via AXI master
    SCHED_PARSE_DESCRIPTOR  = 8'b00000100,  // Parse descriptor fields
    SCHED_READ_PHASE        = 8'b00001000,  // Coordinate read engine
    SCHED_WRITE_PHASE       = 8'b00010000,  // Coordinate write engine
    SCHED_CHAIN_CHECK       = 8'b00100000,  // Check for next descriptor
    SCHED_COMPLETE          = 8'b01000000,  // Transfer complete, report status
    SCHED_ERROR             = 8'b10000000   // Error state
} scheduler_state_t;
```

**Key Differences from RAPIDS:**
- ❌ No credit management (just simple transaction limits)
- ❌ No program engine coordination (no alignment fixup)
- ✅ Simplified FSM (no control read/write phases)

### 5.3 AXI Read Engine (Streaming Pipeline - NO FSM)

**Purpose:** High-performance streaming reads from memory to SRAM buffer

**Architecture:** Pipelined streaming design (NO FSM for performance)

**Key Insight:** FSMs are horrible for performance! Instead, use:
- **Arbiter** selects which channel's `datard_*` interface gets access
- **Streaming pipeline** continuously moves data when granted
- **Data interface** (`datard_valid`, `datard_ready`, `datard_beats_remaining`) controls flow

**Data Read Interface (per channel):**
```systemverilog
// Channel requests read access
input  logic        datard_valid;          // Channel has read request
output logic        datard_ready;          // Engine ready for request
input  logic [63:0] datard_addr;           // Source address (aligned)
input  logic [31:0] datard_beats_remaining; // Beats left to read
input  logic [7:0]  datard_burst_len;      // Preferred burst length
input  logic [3:0]  datard_channel_id;     // Channel ID for tracking
```

**Multiple Versions (Compile-Time Selection):**
1. **Version 1 - Basic:** Single outstanding read, fixed burst length
2. **Version 2 - Pipelined:** Multiple outstanding reads, configurable bursts
3. **Version 3 - Adaptive:** Dynamic burst sizing based on remaining beats

**Operation:**
```
1. Arbiter grants channel access based on priority
2. Engine accepts datard_* request (continuous streaming)
3. AXI AR channel issues read burst
4. AXI R channel streams data → SRAM (no FSM stalls!)
5. Engine updates beats_remaining, accepts next request
6. Different channels can have different burst lengths (e.g., CH0: 8 beats, CH1: 16 beats)
```

**Example: Different Burst Lengths per Channel**
```systemverilog
// Channel 0 prefers 8-beat bursts
datard_burst_len[0] = 8'd8;

// Channel 1 prefers 16-beat bursts
datard_burst_len[1] = 8'd16;

// Engine adapts to requested burst length (within MAX_BURST_LEN)
```

### 5.4 AXI Write Engine (Streaming Pipeline - NO FSM)

**Purpose:** High-performance streaming writes from SRAM buffer to memory

**Architecture:** Pipelined streaming design (NO FSM for performance)

**Key Insight:** Same as read engine - no FSMs! Use streaming pipeline with arbiter.

**Data Write Interface (per channel):**
```systemverilog
// Channel requests write access
input  logic        datawr_valid;           // Channel has write request
output logic        datawr_ready;           // Engine ready for request
input  logic [63:0] datawr_addr;            // Destination address (aligned)
input  logic [31:0] datawr_beats_remaining; // Beats left to write
input  logic [7:0]  datawr_burst_len;       // Preferred burst length
input  logic [3:0]  datawr_channel_id;      // Channel ID for tracking
```

**Multiple Versions (Compile-Time Selection):**
1. **Version 1 - Basic:** Single outstanding write, fixed burst length
2. **Version 2 - Pipelined:** Multiple outstanding writes, configurable bursts
3. **Version 3 - Adaptive:** Dynamic burst sizing based on remaining beats

**Operation:**
```
1. Arbiter grants channel access based on priority
2. Engine accepts datawr_* request (continuous streaming)
3. Engine reads data from SRAM
4. AXI AW channel issues write address
5. AXI W channel streams data (no FSM stalls!)
6. AXI B channel receives response, updates beats_remaining
7. Different channels can have different burst lengths (e.g., CH0: 8 beats, CH2: 32 beats)
```

**Read/Write Asymmetry Example:**
```systemverilog
// Channel can use different burst lengths for read vs write
// Example: Read in small bursts, write in large bursts
datard_burst_len[0] = 8'd8;   // Read: 8 beats
datawr_burst_len[0] = 8'd16;  // Write: 16 beats

// Engine handles asymmetry via SRAM buffering
```

### 5.5 Simple SRAM

**Source:** Direct copy from RAPIDS `simple_sram.sv`

**Purpose:**
- Dual-port SRAM buffer
- Decouples read and write engines
- Shared across all channels (arbitration required)

**Why Reuse:**
- Standard dual-port SRAM design
- Proven in RAPIDS integration tests
- Parameterizable depth and width

---

## 6. Configuration and Control

### 6.1 APB Register Map

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x0000 | `GLOBAL_CTRL` | RW | Global enable, reset |
| 0x0004 | `GLOBAL_STATUS` | RO | Global status, error flags |
| 0x0100 | `CH0_CTRL` | WO | **Channel 0 kick-off** (write descriptor address) |
| 0x0104 | `CH0_STATUS` | RO | Channel 0 status |
| 0x0108 | `CH0_DESC_ADDR` | RO | Channel 0 current descriptor address |
| 0x010C | `CH0_BYTES_XFER` | RO | Channel 0 bytes transferred |
| ... | ... | ... | ... (repeat for channels 1-7) |
| 0x0200 | `CH1_CTRL` | WO | Channel 1 kick-off |
| ... | | | |
| 0x0700 | `CH7_CTRL` | WO | Channel 7 kick-off |

**Kick-Off Sequence:**
1. Software writes descriptor address to `CHx_CTRL` register
2. STREAM fetches descriptor from memory
3. Transfer begins automatically
4. If chained, STREAM follows `next_descriptor_ptr` automatically
5. Completion reported via MonBus packet

### 6.2 Channel Configuration

Each channel independently configurable:
- **Descriptor start address:** Written to `CHx_CTRL`
- **Priority:** Encoded in descriptor (arbitration)
- **Interrupt enable:** Per-descriptor flag
- **Status monitoring:** Read `CHx_STATUS`

---

## 7. Resource Sharing and Arbitration

### 7.1 Shared Resources

**All channels share:**
1. **Descriptor Fetch AXI Master** - Fetches descriptors for all channels
2. **Data Read AXI Master** - Reads source data for all channels
3. **Data Write AXI Master** - Writes destination data for all channels
4. **SRAM Buffer** - Shared buffer (dual-port, but still arbitrated)
5. **MonBus Reporter** - Single monitor output

### 7.2 Arbitration Strategy

**Priority-Based Round-Robin:**
- Channels have priority field in descriptor
- Higher priority = serviced first
- Within same priority: round-robin
- Prevents starvation with timeout

**Example Arbitration:**
```
Channel 0: Priority 7 (highest)
Channel 1: Priority 5
Channel 2: Priority 5
Channel 3: Priority 3
```
Service order: CH0 → CH1 → CH2 (round-robin) → CH0 → CH1 → CH2 → CH3 ...

---

## 8. Error Detection and Recovery

### 8.1 Error Types

| Error Type | Detection | Response |
|------------|-----------|----------|
| **Invalid descriptor** | Valid bit = 0 | Skip, move to next |
| **Alignment error** | Address not aligned | Set error flag, halt channel |
| **AXI SLVERR** | AXI response | Set error flag, halt channel |
| **AXI DECERR** | AXI response | Set error flag, halt channel |
| **Timeout** | Transaction timeout | Set error flag, halt channel |
| **SRAM overflow** | Buffer full | Backpressure, wait |

### 8.2 Error Recovery

**Per-Channel Error Handling:**
- Error sets channel to `CH_ERROR` state
- Channel halts, does not affect other channels
- Software must:
  1. Read `CHx_STATUS` to identify error
  2. Clear error condition
  3. Re-kick channel with new descriptor

**No Automatic Retry:**
- Tutorial design keeps error handling simple
- Software responsible for retry logic

---

## 9. MonBus Integration

### 9.1 Standard MonBus Format

Uses standard 64-bit MonBus packet format:
- [63:60] Packet Type (0=ERROR, 1=COMPL, etc.)
- [59:57] Protocol (custom STREAM protocol)
- [56:53] Event Code (STREAM-specific events)
- [52:47] Channel ID (0-7)
- [46:43] Unit ID (unused for STREAM)
- [42:35] Agent ID (unused for STREAM)
- [34:0] Event Data (address, byte count, etc.)

### 9.2 STREAM Event Codes

| Code | Event | Description |
|------|-------|-------------|
| 0x0 | `DESC_START` | Descriptor started |
| 0x1 | `DESC_COMPLETE` | Descriptor completed |
| 0x2 | `READ_START` | Read phase started |
| 0x3 | `READ_COMPLETE` | Read phase completed |
| 0x4 | `WRITE_START` | Write phase started |
| 0x5 | `WRITE_COMPLETE` | Write phase completed |
| 0x6 | `CHAIN_FETCH` | Chained descriptor fetch |
| 0xF | `ERROR` | Error occurred |

### 9.3 Default Configuration

**Tutorial-Friendly Defaults:**
- **Errors only:** `cfg_error_enable = 1`, all others = 0
- **Interrupts:** Descriptor flag controls per-transfer interrupt
- **Reduces MonBus traffic** for beginner understanding

---

## 10. Design Constraints

### 10.1 Tutorial Constraints (Intentional Simplifications)

| Constraint | Rationale |
|------------|-----------|
| **Aligned addresses only** | Simplify data path, hide alignment complexity |
| **Length in beats** | Avoid byte/chunk conversion math |
| **No circular buffers** | Explicit termination easier to understand |
| **Single APB kick-off** | Simple software model |
| **No credit management** | Avoid exponential encoding complexity |

### 10.2 Implementation Constraints

| Parameter | Value | Notes |
|-----------|-------|-------|
| Max channels | 8 | Compile-time parameter |
| Max burst length | 256 | AXI4 spec limit |
| Descriptor size | 256 bits | 4 × 64-bit words |
| SRAM depth | Parameterizable | Typical: 1024-4096 entries |
| Data width | Parameterizable | Typical: 512-bit |

---

## 11. Verification Strategy

### 11.1 Test Organization

```
projects/components/stream/dv/tests/
├── fub_tests/                  # Functional Unit Block tests
│   ├── descriptor_engine/      # Copy from RAPIDS (adapt imports)
│   ├── scheduler/              # Simplified scheduler tests
│   ├── axi_engines/            # Read/write engine tests
│   └── sram/                   # SRAM tests
│
└── integration_tests/          # Multi-block scenarios
    ├── single_channel/         # Single channel transfers
    ├── multi_channel/          # 8-channel concurrent
    ├── chained_descriptors/    # Descriptor chain tests
    └── error_handling/         # Error recovery tests
```

### 11.2 Test Levels

**Basic (Quick Smoke Tests):**
- Single descriptor, single channel
- Aligned addresses, simple transfers
- ~30 seconds runtime

**Medium (Typical Scenarios):**
- Multiple descriptors, 2-4 channels
- Chained descriptors (2-3 deep)
- ~90 seconds runtime

**Full (Comprehensive Validation):**
- All 8 channels concurrent
- Long descriptor chains (10+ deep)
- Error injection, stress testing
- ~180 seconds runtime

---

## 12. Performance Characteristics

### 12.1 Throughput

**Target:** Match AXI data bus bandwidth

**Factors:**
- SRAM buffer size (limits burst pipelining)
- AXI burst efficiency (engine version selection)
- Channel arbitration overhead
- Descriptor fetch latency

### 12.2 Latency

**Transfer Latency Breakdown:**
- Descriptor fetch: ~10-50 cycles (depends on memory)
- Read phase: `(length / burst_len) × burst_latency`
- Write phase: `(length / burst_len) × burst_latency`
- End-to-end: Typically <200 cycles for small transfers

### 12.3 Resource Utilization (Estimated)

**Target:** <5K LUTs + SRAM

- Descriptor Engine: ~1K LUTs (from RAPIDS)
- Scheduler: ~1K LUTs (simpler than RAPIDS)
- AXI Engines (basic): ~1K LUTs each
- APB Config: ~500 LUTs
- SRAM: Configurable (dominant area)

---

## 13. Development Roadmap

### 13.1 Phase 1: Foundation (Current)
- ✅ Directory structure
- ✅ Package definitions (`stream_pkg.sv`)
- ✅ Imports header (`stream_imports.svh`)
- ⏳ Documentation (this PRD)

### 13.2 Phase 2: Core Blocks
- Adapt descriptor engine from RAPIDS
- Design simplified scheduler
- Create APB config interface
- Copy simple SRAM from RAPIDS

### 13.3 Phase 3: Data Path
- AXI read engine (version 1 - basic)
- AXI write engine (version 1 - basic)
- SRAM integration
- Channel arbitration

### 13.4 Phase 4: Integration
- Top-level module
- MonBus reporter
- Integration testbench
- Single-channel validation

### 13.5 Phase 5: Multi-Channel
- 8-channel support
- Arbiter implementation
- Multi-channel tests
- Performance tuning

### 13.6 Phase 6: Advanced Engines
- AXI engine version 2 (pipelined)
- AXI engine version 3 (burst optimized)
- Performance comparison
- Tutorial documentation

---

## 14. Educational Value

### 14.1 Learning Objectives

**STREAM teaches:**
1. **Descriptor-based DMA design patterns**
   - Descriptor structure and parsing
   - Chained descriptors (scatter-gather)
   - Descriptor fetch via AXI

2. **AXI4 Memory Interface Usage**
   - Burst transactions
   - Address/data/response channels
   - Outstanding transactions

3. **Resource Sharing and Arbitration**
   - Multiple channels sharing AXI masters
   - Priority-based arbitration
   - Conflict resolution

4. **FSM Design and Coordination**
   - Multiple interconnected FSMs
   - State machine composition
   - Error handling

5. **Buffer Management**
   - SRAM-based buffering
   - Rate matching
   - Flow control

### 14.2 Progression Path

**Learning Sequence:**
1. **STREAM (this project):** Memory-to-memory DMA, aligned addresses
2. **STREAM Extended:** Add alignment fixup, more complex scenarios
3. **RAPIDS:** Add network interfaces, credit management, full complexity

---

## 15. Success Criteria

### 15.1 Functional

- ✅ Single descriptor transfer working
- ✅ Chained descriptors (2-3 deep)
- ✅ Multi-channel operation (8 channels concurrent)
- ✅ Error detection and reporting
- ✅ MonBus packet generation
- ✅ >90% functional test coverage

### 15.2 Quality

- ✅ Verilator compiles with 0 warnings
- ✅ All tests passing (100% success rate)
- ✅ Comprehensive documentation
- ✅ Tutorial-quality code comments

### 15.3 Performance

- ✅ Achieves >80% of theoretical AXI bandwidth
- ✅ <5K LUT utilization (excluding SRAM)
- ✅ <200 cycle end-to-end latency for small transfers

---

## 16. Open Questions (For Review)

### 16.1 Descriptor Engine Adaptation
- **Q:** Should descriptor engine use APB-only, RDA-only, or mixed mode?
- **A (pending):** TBD - depends on software use case preference

### 16.2 AXI Descriptor Master
- **Q:** Fixed 256-bit width, or parameterizable?
- **A (pending):** Propose fixed 256-bit for simplicity

### 16.3 Channel Arbitration
- **Q:** Fixed priority, or dynamic priority based on age/fairness?
- **A (pending):** Propose fixed priority with round-robin for tutorial simplicity

### 16.4 SRAM Partitioning
- **Q:** Single shared SRAM, or per-channel SRAMs?
- **A (pending):** Propose single shared SRAM with arbitration (matches RAPIDS pattern)

---

## 17. References

### 17.1 Internal Documentation

- **RAPIDS PRD:** `projects/components/rapids/PRD.md` - Parent architecture
- **RAPIDS Descriptor Engine:** `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`
- **RAPIDS Simple SRAM:** `projects/components/rapids/rtl/rapids_fub/simple_sram.sv`
- **AMBA PRD:** `rtl/amba/PRD.md` - MonBus integration
- **Repository Guide:** `/CLAUDE.md` - Design patterns and conventions

### 17.2 External References

- **AXI4 Specification:** ARM IHI0022E
- **APB Specification:** ARM IHI0024C
- CocoTB Documentation: https://docs.cocotb.org/
- Verilator Manual: https://verilator.org/guide/latest/

---

**Document Version:** 1.0
**Last Updated:** 2025-10-17
**Review Cycle:** Weekly during initial design
**Next Review:** TBD (after user feedback)
**Owner:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** `/PRD.md`
- **Parent Architecture:** `projects/components/rapids/PRD.md`
- **AI Guidance:** `CLAUDE.md` (to be created)
- **Quick Start:** `README.md` (to be created)
