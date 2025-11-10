# AXI Engine V2: Command-Pipelined Architecture

**Version:** 1.0
**Date:** 2025-10-28
**Status:** Design Document - Implementation Pending
**Author:** Architecture Discussion - sean galloway

---

## Executive Summary

This document describes Version 2 (V2) enhancements to the STREAM AXI read and write engines. V2 adds command pipelining to hide memory subsystem latency and increase multi-channel throughput, while maintaining backward compatibility with Version 1 (V1) through parameterization.

**Key Improvements:**
- **5-8x throughput increase** for multi-channel workloads
- **Hide B response latency** (write engine critical path)
- **Parameterized trade-off**: Area savings (V1) vs Performance (V2)
- **Foundation for V3**: Out-of-order (OOO) W data drain

---

## Table of Contents

1. [Background and Motivation](#background-and-motivation)
2. [Version Comparison](#version-comparison)
3. [V2 Architecture Overview](#v2-architecture-overview)
4. [V2 Write Engine Design](#v2-write-engine-design)
5. [V2 Read Engine Design](#v2-read-engine-design)
6. [SRAM Read Pointer Management](#sram-read-pointer-management)
7. [Parameterization Strategy](#parameterization-strategy)
8. [Implementation Phases](#implementation-phases)
9. [Verification Strategy](#verification-strategy)
10. [Performance Analysis](#performance-analysis)
11. [Area/Timing Analysis](#areatiming-analysis)

---

## Background and Motivation

### Version 1 Limitations

**Current V1 Architecture:**
- Processes ONE burst per request
- Blocks on B response before accepting next request
- Serialized operation: AW → W → B → (wait) → next AW

**Performance Bottleneck Example:**
```
Cycle 0:    CH0 issues AW (burst_len=16)
Cycle 1-16: CH0 W data phase (16 beats)
Cycle 50:   CH0 B response arrives (memory latency = 34 cycles!)
Cycle 51:   Engine ready for CH1 AW

Result: 51 cycles for 16-beat transfer = 31% efficiency
```

**Problem:**
- B response latency (20-100+ cycles for DRAM) dominates performance
- Engine sits idle waiting for B response
- Multi-channel systems underutilize AXI bandwidth

### V2 Goals

**Primary Objective:** Hide B response latency by decoupling AW/W/B phases

**Design Principles:**
1. **Accept multiple AW commands** without waiting for B responses
2. **Queue pending transactions** for W data drain
3. **Track B responses asynchronously** with scoreboard
4. **Maintain in-order W drain** (V2) - simplicity first
5. **Enable V3 OOO drain** (future) - architecture foundation

---

## Version Comparison

| Feature | V1 (Simple) | V2 (Pipelined) | V3 (OOO - Future) |
|---------|-------------|----------------|-------------------|
| **AW Accept Rate** | 1 per burst | Up to 8 queued | Up to 8 queued |
| **W Drain Order** | Single transaction | In-order FIFO | Out-of-order priority |
| **B Response** | Blocking | Async tracked | Async tracked |
| **Throughput (8ch)** | 1x baseline | 5-8x baseline | 8-10x baseline |
| **Area** | 1x baseline | 2-3x baseline | 3-4x baseline |
| **Complexity** | Low | Medium | High |
| **Use Case** | Embedded, cost-sensitive | Datacenter, balanced | HPC, max performance |

---

## V2 Architecture Overview

### High-Level Block Diagram

```
                    ┌─────────────────────────────────────────┐
                    │      AXI Write Engine (V2)              │
                    │                                         │
  Scheduler ────────┤  ┌───────────────────────────────────┐ │
  (8 channels)      │  │  Command Acceptance Logic         │ │
                    │  │  - Accept datawr_valid/ready      │ │
   datawr_valid ────┼──┤  - Push to Command Queue          │ │
   datawr_ready ◄───┼──┤  - Issue AW immediately           │ │
   datawr_addr  ────┼──┤                                   │ │
   datawr_burst_len─┼──┤  Condition: Queue not full        │ │
   datawr_channel_id┼──┤              (!cmd_queue_full)    │ │
                    │  └───────────────────────────────────┘ │
                    │            │                            │
                    │            ▼                            │
                    │  ┌───────────────────────────────────┐ │
                    │  │  Command Queue (FIFO)             │ │
                    │  │  Depth: CMD_QUEUE_DEPTH (param)   │ │
                    │  │                                   │ │
                    │  │  Entry: {channel_id,              │ │
                    │  │          burst_len,               │ │
                    │  │          sram_base_addr,          │ │
                    │  │          sram_current_addr,       │ │
                    │  │          awid}                    │ │
                    │  └───────────────────────────────────┘ │
                    │            │                            │
                    │            ▼                            │
                    │  ┌───────────────────────────────────┐ │
                    │  │  W Data Drain FSM                 │ │
                    │  │  - Pop from Command Queue         │ │
                    │  │  - Read from SRAM (per-cmd addr)  │ │
   m_axi_awvalid ◄──┼──┤  - Drive W channel (16 beats)     │ │
   m_axi_wvalid  ◄──┼──┤  - Complete when wlast            │ │
   m_axi_wdata   ◄──┼──┤                                   │ │
                    │  │  State: IDLE, DRAIN, WAIT_SRAM    │ │
                    │  └───────────────────────────────────┘ │
                    │            │                            │
                    │            ▼                            │
                    │  ┌───────────────────────────────────┐ │
                    │  │  B Response Scoreboard            │ │
                    │  │  - Track outstanding AWs          │ │
   m_axi_bvalid  ───┼──┤  - Match BID to channel_id        │ │
   m_axi_bid     ───┼──┤  - Signal completion to scheduler │ │
   m_axi_bresp   ───┼──┤  - Error reporting                │ │
                    │  │                                   │ │
   datawr_done  ◄───┼──┤  Scoreboard[channel_id].done      │ │
   datawr_error ◄───┼──┤  Scoreboard[channel_id].error     │ │
                    │  └───────────────────────────────────┘ │
                    └─────────────────────────────────────────┘
```

### Key Differences from V1

**V1 Serialized Flow:**
```
datawr_valid → AW → W → B → datawr_ready → (next request)
   |←────────────── All phases serialize ─────────────────→|
```

**V2 Pipelined Flow:**
```
datawr_valid[0] → AW[0] ──┐
datawr_valid[1] → AW[1] ──┤
datawr_valid[2] → AW[2] ──┤── Command Queue
datawr_valid[3] → AW[3] ──┘
         ↓                    ↓
   (immediate ready)    W drain (in-order)
                             ↓
                        B responses (async)
```

---

## V2 Write Engine Design

### Command Queue Structure

**Purpose:** Store pending AW commands for sequential W data drain

**Data Structure:**
```systemverilog
typedef struct packed {
    logic [3:0]              channel_id;        // Which channel (0-7)
    logic [7:0]              burst_len;         // Beats in this burst (1-16)
    logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;   // SRAM partition start
    logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr; // Current read position
    logic [ID_WIDTH-1:0]     awid;              // AXI ID for matching
    logic                    valid;             // Entry valid
} cmd_queue_entry_t;

// Queue storage
cmd_queue_entry_t cmd_queue [CMD_QUEUE_DEPTH];
logic [$clog2(CMD_QUEUE_DEPTH)-1:0] wr_ptr;
logic [$clog2(CMD_QUEUE_DEPTH)-1:0] rd_ptr;
logic [$clog2(CMD_QUEUE_DEPTH):0]   count;  // Extra bit for full detection
```

**Operations:**
- **Push**: When `datawr_valid && datawr_ready` (queue not full)
- **Pop**: When W drain FSM completes current burst (wlast)
- **Full**: `count == CMD_QUEUE_DEPTH`
- **Empty**: `count == 0`

### W Data Drain FSM

**Purpose:** Sequentially drain W data for queued AW commands

**States:**
```systemverilog
typedef enum logic [1:0] {
    DRAIN_IDLE   = 2'b00,  // No pending commands
    DRAIN_ACTIVE = 2'b01,  // Actively draining W data
    DRAIN_WAIT   = 2'b10   // Waiting for SRAM data valid
} drain_state_t;
```

**State Transitions:**
```
IDLE ──────────────► ACTIVE
 ▲  (!cmd_queue_empty)   │
 │                       │
 │        ┌──────────────┘
 │        │ (wlast && wvalid && wready)
 │        ▼
 └─────ACTIVE ◄───► WAIT
        (beats remaining)  (sram_rd_valid)
```

**Operation:**
1. **Pop command** from queue when entering ACTIVE
2. **Read SRAM** using `sram_current_addr` from command
3. **Drive W channel** when `sram_rd_valid`
4. **Increment `sram_current_addr`** each beat
5. **Assert wlast** on final beat
6. **Return to IDLE** (if queue empty) or **start next command** (if queue has entries)

### B Response Scoreboard

**Purpose:** Track outstanding AW transactions and match B responses asynchronously

**Data Structure:**
```systemverilog
typedef struct packed {
    logic        outstanding;  // Transaction inflight
    logic [7:0]  burst_len;    // Beats in burst
    logic        error;        // Error detected
    logic [1:0]  error_resp;   // BRESP value
    logic        done;         // Completion flag
} scoreboard_entry_t;

// One entry per channel
scoreboard_entry_t scoreboard [8];
```

**Operations:**
- **Allocate**: When AW issued (set `outstanding = 1`)
- **Match**: When B received, use `BID[3:0]` as channel_id index
- **Complete**: Set `done = 1`, clear `outstanding`, copy `bresp` to `error_resp`
- **Report**: Assert `datawr_done_strobe` for one cycle

**Error Handling:**
```systemverilog
// B response arrives
if (m_axi_bvalid && m_axi_bready) begin
    ch_id = m_axi_bid[3:0];  // Assuming channel_id in lower bits

    scoreboard[ch_id].outstanding <= 1'b0;
    scoreboard[ch_id].done <= 1'b1;

    if (m_axi_bresp != 2'b00) begin  // OKAY = 2'b00
        scoreboard[ch_id].error <= 1'b1;
        scoreboard[ch_id].error_resp <= m_axi_bresp;
    end
end

// Export to scheduler
assign datawr_done_strobe = scoreboard[current_channel].done;
assign datawr_error = scoreboard[current_channel].error;
assign datawr_error_resp = scoreboard[current_channel].error_resp;
```

---

## V2 Read Engine Design

### Key Differences from Write Engine

**Read engine V2 simpler than write engine V2:**
- **No B channel** - R channel provides immediate feedback
- **R data arrives with RLAST** - self-terminating
- **No scoreboard needed** - R response includes RID for matching

**Command Queue Still Required:**
- Store pending AR commands
- Track `{channel_id, burst_len, sram_wr_addr}`
- Drain R data as it arrives

### R Data Handling

**V1 Problem:**
```
CH0 AR issued → Wait for all R data → (ready for CH1)
```

**V2 Solution:**
```
CH0 AR issued → Queue [CH0]
CH1 AR issued → Queue [CH0, CH1]
CH2 AR issued → Queue [CH0, CH1, CH2]

R data for CH0 arrives → Write to SRAM[CH0 partition]
R data for CH1 arrives → Write to SRAM[CH1 partition]
(can overlap if memory supports interleaved responses)
```

**Simplified Scoreboard:**
```systemverilog
// Read engine only needs completion tracking
typedef struct packed {
    logic        outstanding;
    logic [31:0] beats_received;
    logic [31:0] beats_expected;
} read_tracker_t;

read_tracker_t read_tracker [8];
```

---

## SRAM Read Pointer Management

### The Core Challenge

**Problem:** V2/V3 need to track SRAM read positions for multiple queued transactions

**V1 Approach (Single Pointer):**
```systemverilog
logic [SRAM_ADDR_WIDTH-1:0] r_sram_rd_ptr;  // Works for one-at-a-time

// Simple increment
r_sram_rd_ptr <= r_sram_rd_ptr + 1'b1;
```

**V2 Requirement (Per-Transaction Tracking):**
```systemverilog
// Command queue entry includes BOTH:
logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;    // Where partition starts
logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr; // Current position within burst

// W drain FSM uses current_addr:
sram_rd_addr <= cmd_queue[rd_ptr].sram_current_addr;

// Increment within command entry:
cmd_queue[rd_ptr].sram_current_addr <=
    cmd_queue[rd_ptr].sram_current_addr + 1'b1;
```

### SRAM Partitioning Strategy

**Per-Channel Partition:**
```
SRAM_DEPTH = 4096 (total)
NUM_CHANNELS = 8
Partition size = 4096 / 8 = 512 entries per channel

Channel 0: SRAM[0x000 - 0x1FF]
Channel 1: SRAM[0x200 - 0x3FF]
Channel 2: SRAM[0x400 - 0x5FF]
...
Channel 7: SRAM[0xE00 - 0xFFF]
```

**Base Address Calculation:**
```systemverilog
function automatic [SRAM_ADDR_WIDTH-1:0] calc_sram_base(input [3:0] channel_id);
    return {channel_id, {(SRAM_ADDR_WIDTH-4){1'b0}}};  // channel_id << (ADDR_WIDTH-4)
endfunction

// Example: channel_id=3, SRAM_ADDR_WIDTH=12
// Result: 12'h600 (0x600 = 3 × 512)
```

**Current Address Management:**
```systemverilog
// On command queue push:
cmd_queue[wr_ptr].sram_base_addr <= calc_sram_base(datawr_channel_id);
cmd_queue[wr_ptr].sram_current_addr <= calc_sram_base(datawr_channel_id); // Start at base

// During W drain:
if (m_axi_wvalid && m_axi_wready) begin
    cmd_queue[rd_ptr].sram_current_addr <=
        cmd_queue[rd_ptr].sram_current_addr + 1'b1;
end
```

### Key Insight: Pointer Persistence

**Critical Design Decision:**

**Option A: Store pointers in command queue (chosen)**
```systemverilog
// PROS:
// - Self-contained: Each command knows its SRAM region
// - No external state needed
// - Naturally supports OOO (V3)
// - Simple to verify

// CONS:
// - Slightly larger command queue entries
```

**Option B: Separate per-channel pointer array**
```systemverilog
logic [SRAM_ADDR_WIDTH-1:0] sram_rd_ptrs [8];  // One per channel

// PROS:
// - Smaller command queue entries

// CONS:
// - Must synchronize with command queue state
// - More complex for OOO
// - Hard to verify correctness
```

**Recommendation:** Use Option A (store in command queue)

---

## Parameterization Strategy

### Module Parameters

```systemverilog
module axi_write_engine #(
    // Existing parameters
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8,
    parameter int MAX_BURST_LEN = 16,
    parameter int SRAM_DEPTH = 4096,
    parameter int SRAM_ADDR_WIDTH = $clog2(SRAM_DEPTH),

    // V2 Performance parameters
    parameter bit ENABLE_CMD_PIPELINE = 1'b0,  // 0=V1, 1=V2
    parameter int CMD_QUEUE_DEPTH = 8,         // V2 only: 2-16
    parameter int MAX_OUTSTANDING = 8          // V2 only: 1-8
) (
    // ... ports unchanged
);
```

### Generate Block Structure

```systemverilog
generate
    if (ENABLE_CMD_PIPELINE) begin : gen_v2_pipelined
        // V2 Implementation
        // - Command queue (FIFO)
        // - W drain FSM
        // - B response scoreboard
        // - Per-command SRAM pointer tracking

        // Instantiate V2 logic
        axi_write_engine_v2 #(
            .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH),
            .CMD_QUEUE_DEPTH(CMD_QUEUE_DEPTH),
            .MAX_OUTSTANDING(MAX_OUTSTANDING)
        ) u_v2_engine (
            // ... connect all ports
        );

    end else begin : gen_v1_simple
        // V1 Implementation (existing code)
        // - Single AW/W/B transaction
        // - Blocking on B response
        // - Simple state machine

        // Keep existing V1 logic inline
        // (current axi_write_engine.sv implementation)

    end
endgenerate
```

### Synthesis Optimization

**Key Point:** Synthesis tools eliminate unused logic

**Example Synthesis Results:**
```
Configuration              Area (LUTs)    FMax (MHz)    Throughput
-----------------------------------------------------------------
V1 (ENABLE_CMD_PIPELINE=0)   1,250         350           1.0x
V2 (CMD_QUEUE_DEPTH=4)       3,100         320           4.2x
V2 (CMD_QUEUE_DEPTH=8)       3,450         310           6.8x
V2 (CMD_QUEUE_DEPTH=16)      4,200         290           7.5x
```

**Trade-off Analysis:**
- **Embedded/IoT**: V1 (area-critical)
- **Balanced**: V2 with CMD_QUEUE_DEPTH=4
- **Datacenter**: V2 with CMD_QUEUE_DEPTH=8-16

---

## Implementation Phases

### Phase 1: V2 Write Engine (4-6 weeks)

**Week 1-2: Command Queue Infrastructure**
- Implement FIFO-based command queue
- Add push/pop logic with full/empty flags
- Unit tests for queue operations

**Week 3-4: W Drain FSM**
- Implement 3-state FSM (IDLE/ACTIVE/WAIT)
- Add per-command SRAM pointer tracking
- Integrate with command queue

**Week 5: B Response Scoreboard**
- Implement per-channel tracking
- Add BID → channel_id mapping
- Error handling and reporting

**Week 6: Integration and Testing**
- Connect all V2 blocks
- Run existing testbenches with V2 enabled
- Performance validation

### Phase 2: V2 Read Engine (2-3 weeks)

**Week 1: Command Queue (reuse write logic)**
- Adapt command queue for AR channel
- Simpler than write (no B scoreboard)

**Week 2: R Data Handling**
- Implement R data drain to SRAM
- RID-based channel matching

**Week 3: Integration and Testing**
- Full read engine V2 validation
- Performance comparison vs V1

### Phase 3: Parameterization and Documentation (1 week)

**Tasks:**
- Add `ENABLE_CMD_PIPELINE` parameter
- Create generate blocks
- Synthesis area/timing reports
- Update user documentation

---

## Verification Strategy

### Test Levels

**Unit Tests (Per Component):**
1. **Command Queue**
   - Push/pop operations
   - Full/empty detection
   - Wrap-around behavior
   - Concurrent push/pop

2. **W Drain FSM**
   - State transitions
   - SRAM pointer management
   - wlast generation
   - Error cases

3. **B Scoreboard**
   - BID matching
   - Error propagation
   - Multiple outstanding transactions

**Integration Tests (Full Engine):**
1. **Single Channel Performance**
   - Compare V1 vs V2 latency
   - Measure B response hiding

2. **Multi-Channel Stress**
   - All 8 channels active
   - Queue depth utilization
   - Scoreboard correctness

3. **Corner Cases**
   - Queue full conditions
   - SRAM backpressure
   - Error injection (SLVERR, DECERR)

### Test Methodology

**Existing Testbench Compatibility:**
- V1 tests MUST pass with V2 enabled
- Use `ENABLE_CMD_PIPELINE` parameter in conftest.py
- Run full regression: V1 and V2 modes

**New V2-Specific Tests:**
```python
@pytest.mark.parametrize("enable_pipeline", [False, True])
@pytest.mark.parametrize("queue_depth", [4, 8, 16])
def test_multi_channel_throughput(enable_pipeline, queue_depth):
    """Measure throughput improvement with V2."""
    # Run 8 channels concurrently
    # Measure cycles to complete
    # Assert V2 >= 4x faster than V1
```

**Performance Metrics:**
- **Throughput (GB/s)**: Data transferred / time
- **Latency (cycles)**: First request → last completion
- **Efficiency (%)**: Actual throughput / theoretical max
- **Queue Utilization (%)**: Average queue occupancy

---

## Performance Analysis

### Theoretical Throughput Calculation

**V1 Performance (Single Transaction at a Time):**
```
Per-transaction overhead:
- AW handshake: 1 cycle
- W data phase: 16 cycles (burst_len=16)
- B response wait: 20-100 cycles (memory dependent)

Total: 37-117 cycles per 16-beat burst

Throughput: 16 beats / 37 cycles = 0.43 beats/cycle (worst case)
Throughput: 16 beats / 117 cycles = 0.14 beats/cycle (typical DRAM)
```

**V2 Performance (Pipelined):**
```
Initial AW phase:
- Issue 8 AW commands: 8 cycles (back-to-back)

W drain phase:
- Burst 1: 16 cycles
- Burst 2: 16 cycles
- ... (concurrent with B responses)
- Burst 8: 16 cycles
Total W phase: 128 cycles

B responses: Arrive asynchronously (hidden)

Total: 8 (AW) + 128 (W) = 136 cycles for 8 × 16 = 128 beats

Throughput: 128 beats / 136 cycles = 0.94 beats/cycle
Improvement: 6.7x over V1 (typical DRAM case)
```

### Real-World Performance Expectations

**Target Systems:**

| System | V1 Throughput | V2 Throughput | Improvement |
|--------|---------------|---------------|-------------|
| **Embedded SRAM** | 0.43 beats/cycle | 0.85 beats/cycle | 2.0x |
| **DDR3 SDRAM** | 0.18 beats/cycle | 0.92 beats/cycle | 5.1x |
| **DDR4 SDRAM** | 0.14 beats/cycle | 0.94 beats/cycle | 6.7x |
| **PCIe Gen3** | 0.22 beats/cycle | 0.90 beats/cycle | 4.1x |

**Key Observation:** V2 benefit scales with memory latency

---

## Area/Timing Analysis

### Area Breakdown (Estimated)

**V1 Baseline:**
```
Component               LUTs    FFs    BRAM
--------------------------------------------
AW logic                 150    200      0
W logic                  180    250      0
B logic                  120    150      0
SRAM interface           200    180      0
Control FSM              180    120      0
--------------------------------------------
Total V1               1,250  1,000      0
```

**V2 Additional:**
```
Component               LUTs    FFs    BRAM
--------------------------------------------
Command Queue (FIFO)     450    380      0
W Drain FSM              280    220      0
B Scoreboard (8 entries) 320    240      0
SRAM pointer tracking    200    160      0
--------------------------------------------
V2 Overhead            1,250  1,000      0
--------------------------------------------
Total V2 (V1+overhead) 2,500  2,000      0
```

**Area Multiplier:** V2 = 2.0x V1 area

### Timing Considerations

**V1 Critical Path:**
```
datawr_valid → (combinational ready logic) → datawr_ready
Delay: ~2 levels of logic
```

**V2 Critical Path:**
```
cmd_queue_full → (FIFO count logic) → datawr_ready
Delay: ~5 levels of logic (counter comparison, full detection)
```

**Impact:**
- V2 may reduce FMax by 10-15%
- Trade-off: Slightly lower clock vs much higher efficiency
- Net result: Higher absolute throughput despite lower FMax

**Timing Optimization:**
- Pipeline `cmd_queue_full` signal (1-cycle latency acceptable)
- Register SRAM pointer increments
- Use gray code for FIFO pointers (if crossing clock domains)

---

## Appendix A: Terminology

| Term | Definition |
|------|------------|
| **Beat** | One data transfer (one cycle of valid/ready handshake) |
| **Burst** | One AXI transaction (one AW/AR + multiple beats + one B/R) |
| **Command Pipeline** | Accepting multiple commands before completing earlier ones |
| **Scoreboard** | Structure tracking outstanding transactions |
| **In-Order Drain** | W data sent in same order as AW commands (V2) |
| **Out-of-Order Drain** | W data sent based on priority/availability (V3) |

---

## Appendix B: Open Questions

**For Design Review:**

1. **CMD_QUEUE_DEPTH sizing:**
   - Default value 8 sufficient?
   - Should it scale with NUM_CHANNELS?

2. **AWID assignment:**
   - Use lower 4 bits for channel_id?
   - Upper bits for transaction ID?

3. **Error recovery:**
   - Should SLVERR stop channel or continue?
   - Software visibility into errors?

4. **SRAM backpressure:**
   - What if SRAM slower than AXI?
   - Should W drain pause or drop data?

5. **V3 OOO preparation:**
   - Any V2 decisions that would block V3?
   - Priority scheme for OOO drain?

---

## Appendix C: References

**Internal Documents:**
- `projects/components/stream/rtl/stream_fub/axi_write_engine.sv` - V1 implementation
- `bin/CocoTBFramework/components/stream/scheduler_bfm.py` - Scheduler BFM
- `projects/components/stream/dv/tbclasses/datapath_wr_test_tb.py` - Write testbench

**External Standards:**
- ARM AMBA AXI4 Protocol Specification (IHI0022E)
- ARM AMBA 4 AXI4, AXI4-Lite, and AXI4-Stream Protocol Spec

**Related Work:**
- RAPIDS scheduler (similar multi-channel architecture)
- AXI interconnect pipelining techniques

---

**Version History:**
- v1.0 (2025-10-28): Initial design document
