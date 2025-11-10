# SRAM Read Pointer Management Analysis
## Multi-Channel Out-of-Order Operation

**Version:** 1.0
**Date:** 2025-10-28
**Purpose:** Analyze SRAM pointer management for V2/V3 AXI engines
**Author:** Architecture Discussion - sean galloway

---

## Executive Summary

This document analyzes SRAM read pointer management requirements for V2 (command-pipelined) and V3 (out-of-order) AXI write engines. The core challenge is tracking multiple independent read positions when draining W data from per-channel SRAM partitions.

**Key Findings:**
1. ✅ **V1 single-pointer approach insufficient** for V2/V3
2. ✅ **Per-command pointer tracking required** (embedded in command queue)
3. ✅ **Per-channel SRAM partitioning enables OOO** without data hazards
4. ✅ **Command queue design naturally supports V3 OOO** with minimal changes

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [V1 Architecture Analysis](#v1-architecture-analysis)
3. [V2 Requirements](#v2-requirements)
4. [Proposed Solution](#proposed-solution)
5. [V3 OOO Compatibility](#v3-ooo-compatibility)
6. [Implementation Details](#implementation-details)
7. [Verification Strategy](#verification-strategy)
8. [Performance Impact](#performance-impact)

---

## Problem Statement

### The Core Challenge

**Question:** How does the AXI write engine track SRAM read positions when multiple W data drain operations are queued/active?

**Example Scenario:**
```
Time 0:  CH0 issues AW (16 beats, SRAM[0x000-0x00F])
Time 1:  CH1 issues AW (16 beats, SRAM[0x200-0x20F])
Time 2:  CH2 issues AW (8 beats,  SRAM[0x400-0x407])

         Command Queue: [CH0, CH1, CH2]

Time 3:  Start draining CH0 W data
         - Read SRAM[0x000] → Send W beat 0
         - Read SRAM[0x001] → Send W beat 1
         ...
         - Read SRAM[0x00F] → Send W beat 15 (wlast)

Time 19: CH0 complete, start draining CH1 W data
         - Must read SRAM[0x200], NOT 0x010!
         - CH1's SRAM partition is 0x200-0x3FF
         - Cannot continue from CH0's pointer!
```

**The Issue:** A single global SRAM read pointer cannot track independent positions for multiple queued commands.

---

## V1 Architecture Analysis

### Current V1 Implementation

**From `axi_write_engine.sv` (lines 143-144):**
```systemverilog
// Single SRAM read pointer
logic [SRAM_ADDR_WIDTH-1:0] r_sram_rd_ptr;
logic r_sram_rd_req;
```

**V1 Operation:**
1. Accept ONE request (datawr_valid && datawr_ready)
2. Initialize `r_sram_rd_ptr` to channel's SRAM base address
3. Increment `r_sram_rd_ptr` for each W beat sent
4. Complete W phase, wait for B response
5. Accept NEXT request (reset pointer for new channel)

**Why V1 Works:**
- Only ONE transaction inflight at any time
- Single pointer tracks current transaction
- Each new transaction resets pointer to new channel's base

**Example V1 Timeline:**
```
Cycle 0:   CH0 request → r_sram_rd_ptr = 0x000
Cycle 1-16: W drain → r_sram_rd_ptr increments 0x000→0x00F
Cycle 50:  B response arrives
Cycle 51:  CH1 request → r_sram_rd_ptr = 0x200 (reset!)
Cycle 52-67: W drain → r_sram_rd_ptr increments 0x200→0x20F
```

**Key Observation:** Pointer reset between transactions masks the issue.

---

## V2 Requirements

### Multi-Command Tracking

**V2 Scenario (Pipelined Commands):**
```
Cycle 0:  CH0 AW issued → Queue: [CH0 @ 0x000]
Cycle 1:  CH1 AW issued → Queue: [CH0 @ 0x000, CH1 @ 0x200]
Cycle 2:  CH2 AW issued → Queue: [CH0 @ 0x000, CH1 @ 0x200, CH2 @ 0x400]

Cycle 3:  Start draining CH0
          - Need to track: "Currently draining CH0, position 0x000"

Cycle 4:  CH0 drain continues
          - Need to track: "Currently draining CH0, position 0x001"
          ...

Cycle 18: CH0 complete, start draining CH1
          - Need to track: "Currently draining CH1, position 0x200"
          - MUST NOT use position 0x012 (where CH0 left off!)
```

**Requirements:**
1. **Per-command state:** Each queued command needs its own SRAM pointer
2. **Independent tracking:** CH0's progress doesn't affect CH1's starting position
3. **Persistence:** Pointer state must survive while command is queued (not draining)

### Naive Approach (Doesn't Work)

**Attempt: Per-Channel Pointer Array**
```systemverilog
logic [SRAM_ADDR_WIDTH-1:0] sram_rd_ptrs [8];  // One per channel

// On command queue push:
cmd_queue[wr_ptr].channel_id <= datawr_channel_id;

// On W drain:
sram_rd_addr <= sram_rd_ptrs[current_channel_id];  // ❌ PROBLEM!
```

**Why This Fails:**
- Channel can issue MULTIPLE commands before first completes
- Example: CH0 issues 3 commands (3 bursts) → Queue: [CH0, CH0, CH0]
- Single `sram_rd_ptrs[0]` cannot track 3 independent positions!

**Correct Understanding:**
- Need **per-TRANSACTION tracking**, not per-channel
- A channel can have multiple transactions queued

---

## Proposed Solution

### Design: Embed Pointers in Command Queue

**Command Queue Entry Structure:**
```systemverilog
typedef struct packed {
    logic [3:0]              channel_id;        // Which channel (0-7)
    logic [7:0]              burst_len;         // Beats in this burst
    logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;   // Partition start
    logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr; // ★ Current read position
    logic [ID_WIDTH-1:0]     awid;              // AXI ID
    logic                    valid;             // Entry valid
} cmd_queue_entry_t;

cmd_queue_entry_t cmd_queue [CMD_QUEUE_DEPTH];
```

**Key Fields:**
- `sram_base_addr`: Where channel's SRAM partition starts (constant per channel)
- `sram_current_addr`: Current read position within this burst (increments during drain)

### Operation Flow

**1. Command Queue Push (AW Acceptance):**
```systemverilog
// Calculate SRAM base address for this channel
function automatic [SRAM_ADDR_WIDTH-1:0] calc_sram_base(input [3:0] ch_id);
    localparam int PARTITION_SIZE = SRAM_DEPTH / 8;
    return ch_id * PARTITION_SIZE;
endfunction

// On datawr_valid && datawr_ready:
cmd_queue[wr_ptr].channel_id <= datawr_channel_id;
cmd_queue[wr_ptr].burst_len <= w_capped_burst_len;

// Initialize both base and current to partition start
cmd_queue[wr_ptr].sram_base_addr <= calc_sram_base(datawr_channel_id);
cmd_queue[wr_ptr].sram_current_addr <= calc_sram_base(datawr_channel_id);

cmd_queue[wr_ptr].valid <= 1'b1;
wr_ptr <= wr_ptr + 1'b1;
```

**2. W Data Drain:**
```systemverilog
// Read from current command's SRAM position
assign sram_rd_addr = cmd_queue[rd_ptr].sram_current_addr;
assign sram_rd_en = (drain_state == DRAIN_ACTIVE);

// Increment SRAM pointer on each W beat transfer
always_ff @(posedge clk) begin
    if (m_axi_wvalid && m_axi_wready) begin
        cmd_queue[rd_ptr].sram_current_addr <=
            cmd_queue[rd_ptr].sram_current_addr + 1'b1;
    end
end
```

**3. Command Completion:**
```systemverilog
// On wlast, pop command from queue
if (m_axi_wvalid && m_axi_wready && m_axi_wlast) begin
    cmd_queue[rd_ptr].valid <= 1'b0;
    rd_ptr <= rd_ptr + 1'b1;
    // Next command's sram_current_addr is already initialized!
end
```

### Example Execution Trace

**Setup:**
```
SRAM Partitions (SRAM_DEPTH=4096, 8 channels, 512 entries each):
CH0: 0x000 - 0x1FF
CH1: 0x200 - 0x3FF
CH2: 0x400 - 0x5FF
```

**Execution:**
```
Cycle 0:  CH0 AW (burst_len=16)
          Queue[0]: {ch_id=0, burst=16, base=0x000, current=0x000}

Cycle 1:  CH1 AW (burst_len=8)
          Queue[0]: {ch_id=0, burst=16, base=0x000, current=0x000}
          Queue[1]: {ch_id=1, burst=8,  base=0x200, current=0x200}

Cycle 2:  CH0 AW (burst_len=12) ← Second request from CH0!
          Queue[0]: {ch_id=0, burst=16, base=0x000, current=0x000}
          Queue[1]: {ch_id=1, burst=8,  base=0x200, current=0x200}
          Queue[2]: {ch_id=0, burst=12, base=0x000, current=0x000} ← Independent!

Cycle 3:  Start draining Queue[0] (CH0, first burst)
          sram_rd_addr = 0x000
          W beat sent
          Queue[0].current_addr = 0x001

Cycle 4:  Continue draining Queue[0]
          sram_rd_addr = 0x001
          W beat sent
          Queue[0].current_addr = 0x002
          ...

Cycle 18: Queue[0] complete (wlast)
          Pop Queue[0], rd_ptr = 1
          Start draining Queue[1] (CH1)
          sram_rd_addr = Queue[1].current_addr = 0x200 ✅ Correct!

Cycle 26: Queue[1] complete
          Pop Queue[1], rd_ptr = 2
          Start draining Queue[2] (CH0, second burst)
          sram_rd_addr = Queue[2].current_addr = 0x000 ✅ Correct restart!
```

**Key Observation:** Each queue entry has independent `current_addr`, enabling:
- Multiple commands from same channel
- Different starting positions per command
- Natural V3 OOO support (see next section)

---

## V3 OOO Compatibility

### Innate OOO Support

**User's Claim:** "Due to the way I've architected the structures, they are innately OOO compatible already."

**Analysis:** ✅ **CORRECT!** The proposed design IS OOO-friendly.

### Why V3 OOO Works

**V2 Design Assumptions:**
1. ✅ Per-channel SRAM partitioning (no cross-channel hazards)
2. ✅ Command queue stores all per-transaction state
3. ✅ Each entry has independent `sram_current_addr`
4. ✅ W drain can pop from any queue entry (not just head)

**V3 OOO Requirements:**
- **Arbitrary drain order**: Pick any command from queue (not FIFO order)
- **SRAM data availability**: Check if SRAM has data before draining
- **AWID matching**: Ensure W data matches issued AW's ID

**V3 Modification (Minimal Changes to V2):**

**V2: FIFO Pop**
```systemverilog
// Always drain from head
assign current_cmd = cmd_queue[rd_ptr];
```

**V3: Priority-Based Select**
```systemverilog
// Select highest-priority ready command
function automatic int select_ooo_cmd();
    for (int i = 0; i < CMD_QUEUE_DEPTH; i++) begin
        if (cmd_queue[i].valid &&
            sram_has_data(cmd_queue[i].channel_id) &&
            !cmd_queue[i].draining) begin
            return i;  // First ready command
        end
    end
    return -1;  // None ready
endfunction

assign current_cmd_idx = select_ooo_cmd();
assign current_cmd = cmd_queue[current_cmd_idx];
```

**Additional V3 State:**
```systemverilog
typedef struct packed {
    // ... existing fields ...
    logic draining;  // Currently being drained (prevent re-selection)
} cmd_queue_entry_t;
```

### V3 Example Scenario

**Scenario: CH1 SRAM ready, CH0 SRAM empty**

```
Queue State:
[0]: {ch_id=0, burst=16, base=0x000, current=0x005, draining=0} ← Stalled (no SRAM data)
[1]: {ch_id=1, burst=8,  base=0x200, current=0x200, draining=0} ← Ready (SRAM full)
[2]: {ch_id=2, burst=12, base=0x400, current=0x400, draining=0} ← Not checked yet

V2 Behavior:
- Drain [0] (FIFO order)
- Stall waiting for CH0 SRAM data
- [1] and [2] blocked

V3 Behavior:
- Check SRAM status for all queued commands
- Skip [0] (SRAM empty)
- Drain [1] (SRAM ready) ← Start immediately!
- When [0] SRAM fills, resume [0]
```

**Benefits:**
- Hide SRAM fill latency
- Better SRAM utilization
- Higher effective throughput

### Remaining V3 Challenges

**1. SRAM Data Availability Checking:**
```systemverilog
// Need to query: "Does channel X have Y beats ready in SRAM?"
function automatic logic sram_has_data(input [3:0] ch_id, input [7:0] beats_needed);
    logic [12:0] ch_count;
    ch_count = sram_wr_count[ch_id];  // From SRAM controller
    return (ch_count >= beats_needed);
endfunction
```

**2. AWID Assignment for OOO:**
```systemverilog
// Must ensure W data matches AW's ID
// Option A: Use queue index as transaction ID
assign cmd_queue[i].awid = {4'h0, i[3:0]};  // Upper bits = 0, lower = queue index

// When draining:
assign m_axi_wid = current_cmd.awid;  // ← Critical: Match W to AW!
```

**3. B Response Matching:**
```systemverilog
// Scoreboard must use AWID (not channel_id) as key
// Since same channel can have multiple AWs inflight

scoreboard_entry_t scoreboard [CMD_QUEUE_DEPTH];  // Index by AWID, not channel!
```

**Conclusion:** V3 OOO is indeed naturally supported with minor extensions to V2 infrastructure.

---

## Implementation Details

### SRAM Partition Calculation

**Formula:**
```systemverilog
localparam int NUM_CHANNELS = 8;
localparam int PARTITION_SIZE = SRAM_DEPTH / NUM_CHANNELS;
localparam int PARTITION_ADDR_BITS = $clog2(PARTITION_SIZE);

// Base address: channel_id * PARTITION_SIZE
function automatic [SRAM_ADDR_WIDTH-1:0] calc_sram_base(input [3:0] ch_id);
    return {{(SRAM_ADDR_WIDTH-PARTITION_ADDR_BITS){1'b0}}, ch_id} << PARTITION_ADDR_BITS;
endfunction
```

**Example (SRAM_DEPTH=4096, 8 channels):**
```
PARTITION_SIZE = 4096 / 8 = 512 entries
PARTITION_ADDR_BITS = $clog2(512) = 9 bits

CH0: calc_sram_base(0) = 12'b0000_0000_0000 = 0x000
CH1: calc_sram_base(1) = 12'b0010_0000_0000 = 0x200
CH2: calc_sram_base(2) = 12'b0100_0000_0000 = 0x400
...
CH7: calc_sram_base(7) = 12'b1110_0000_0000 = 0xE00
```

### Pointer Increment Logic

**During W Drain:**
```systemverilog
// State: DRAIN_ACTIVE
// current_cmd points to active queue entry

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        // Reset handled at queue level
    end else begin
        // Increment on successful W beat transfer
        if (drain_state == DRAIN_ACTIVE &&
            m_axi_wvalid && m_axi_wready) begin

            // Increment current command's SRAM pointer
            cmd_queue[rd_ptr].sram_current_addr <=
                cmd_queue[rd_ptr].sram_current_addr + 1'b1;

            // Check for completion
            if (m_axi_wlast) begin
                // Don't reset pointer - command will be popped
                drain_state <= DRAIN_IDLE;
            end
        end
    end
end
```

### Boundary Checking (Safety)

**Ensure pointers don't exceed partition bounds:**
```systemverilog
// Paranoid safety check (synthesis should optimize if impossible)
always_comb begin
    // Extract partition ID from current_addr (upper bits)
    logic [3:0] addr_partition_id;
    addr_partition_id = cmd_queue[rd_ptr].sram_current_addr[SRAM_ADDR_WIDTH-1:PARTITION_ADDR_BITS];

    // Compare to expected channel_id
    assert (addr_partition_id == cmd_queue[rd_ptr].channel_id)
        else $error("SRAM pointer crossed partition boundary!");
end
```

---

## Verification Strategy

### Unit Tests

**Test 1: Single Channel Multiple Bursts**
```python
async def test_single_channel_multiple_bursts(tb):
    """Verify independent SRAM pointers for same channel."""
    # Issue 3 bursts from CH0
    await tb.issue_write_request(ch_id=0, addr=0x1000, beats=16, burst_len=16)
    await tb.issue_write_request(ch_id=0, addr=0x2000, beats=16, burst_len=16)
    await tb.issue_write_request(ch_id=0, addr=0x3000, beats=16, burst_len=16)

    # Verify: All 3 commands queued with base=0x000
    assert tb.cmd_queue[0].sram_base_addr == 0x000
    assert tb.cmd_queue[1].sram_base_addr == 0x000
    assert tb.cmd_queue[2].sram_base_addr == 0x000

    # Verify: All 3 have independent current_addr
    assert tb.cmd_queue[0].sram_current_addr == 0x000
    assert tb.cmd_queue[1].sram_current_addr == 0x000  # Not 0x010!
    assert tb.cmd_queue[2].sram_current_addr == 0x000  # Not 0x020!

    # Wait for completion
    await tb.wait_for_completion(timeout=1000)

    # Verify: Correct SRAM regions read
    assert tb.sram_accesses[0x000:0x00F] == 16  # First burst
    assert tb.sram_accesses[0x000:0x00F] == 16  # Second burst (same region!)
    assert tb.sram_accesses[0x000:0x00F] == 16  # Third burst (same region!)
```

**Test 2: Multi-Channel Interleaved**
```python
async def test_multi_channel_interleaved(tb):
    """Verify correct SRAM partitioning."""
    # Issue bursts from CH0, CH1, CH2
    await tb.issue_write_request(ch_id=0, addr=0x1000, beats=16, burst_len=16)
    await tb.issue_write_request(ch_id=1, addr=0x2000, beats=8, burst_len=8)
    await tb.issue_write_request(ch_id=2, addr=0x3000, beats=12, burst_len=12)

    # Verify: Different SRAM base addresses
    assert tb.cmd_queue[0].sram_base_addr == 0x000  # CH0 partition
    assert tb.cmd_queue[1].sram_base_addr == 0x200  # CH1 partition
    assert tb.cmd_queue[2].sram_base_addr == 0x400  # CH2 partition

    # Wait for completion
    await tb.wait_for_completion(timeout=1000)

    # Verify: Correct SRAM regions accessed
    assert tb.sram_accesses[0x000:0x00F] == 16  # CH0 data
    assert tb.sram_accesses[0x200:0x207] == 8   # CH1 data
    assert tb.sram_accesses[0x400:0x40B] == 12  # CH2 data
```

**Test 3: Pointer Persistence**
```python
async def test_pointer_persistence_during_queue(tb):
    """Verify current_addr doesn't change while queued."""
    # Queue 3 commands
    await tb.issue_write_request(ch_id=0, addr=0x1000, beats=16, burst_len=16)
    await tb.issue_write_request(ch_id=1, addr=0x2000, beats=16, burst_len=16)
    await tb.issue_write_request(ch_id=2, addr=0x3000, beats=16, burst_len=16)

    # Start draining first command
    # ... drain ongoing ...

    # While draining Queue[0], check Queue[1] and Queue[2] unchanged
    for cycle in range(16):
        await tb.wait_clocks('clk', 1)
        # Queue[1] and Queue[2] should have original current_addr
        assert tb.cmd_queue[1].sram_current_addr == 0x200
        assert tb.cmd_queue[2].sram_current_addr == 0x400
```

### Integration Tests

**Test 4: V2 Full Pipeline**
```python
@pytest.mark.parametrize("num_channels", [1, 4, 8])
async def test_v2_full_pipeline(tb, num_channels):
    """Test V2 with all channels active."""
    # Issue commands to all channels
    for ch in range(num_channels):
        await tb.issue_write_request(ch_id=ch, addr=0x1000*ch, beats=64, burst_len=16)

    # Verify: All commands queued
    assert tb.cmd_queue_count == num_channels

    # Wait for all completions
    await tb.wait_for_all_completions(timeout=5000)

    # Verify: All SRAM partitions accessed correctly
    for ch in range(num_channels):
        base = ch * 512  # PARTITION_SIZE
        assert tb.sram_accesses[base:base+63] == 64
```

---

## Performance Impact

### Memory Overhead

**Command Queue Entry Size:**
```
channel_id:        4 bits
burst_len:         8 bits
sram_base_addr:   12 bits (for SRAM_DEPTH=4096)
sram_current_addr: 12 bits ← Additional field
awid:              8 bits
valid:             1 bit
--------------------------------
Total:            45 bits per entry

CMD_QUEUE_DEPTH=8:
Total storage: 45 × 8 = 360 bits = ~45 bytes
```

**Comparison to Per-Channel Array:**
```
Per-channel pointer array:
sram_rd_ptrs[8]: 12 bits × 8 = 96 bits

Command queue approach:
360 bits (for full entry storage)

Overhead: 360 - 96 = 264 additional bits
```

**Trade-off:** Small area increase (264 bits) for massive flexibility (V3 OOO support).

### Timing Impact

**V1 SRAM Address Path:**
```
r_sram_rd_ptr ──► sram_rd_addr
Delay: Direct register output (minimal)
```

**V2 SRAM Address Path:**
```
cmd_queue[rd_ptr].sram_current_addr ──► sram_rd_addr
Delay: Memory array read + mux (1-2 logic levels)
```

**Impact:** ~0.5-1.0 ns additional delay
- Negligible for typical 100-250 MHz clock rates
- Can register if needed (1-cycle SRAM address latency acceptable)

---

## Conclusions

### Summary of Findings

1. ✅ **V1 single-pointer insufficient** for V2/V3 multi-command operation
2. ✅ **Embedded per-command pointers** (in queue entries) optimal solution
3. ✅ **Per-channel SRAM partitioning** prevents cross-channel hazards
4. ✅ **Design naturally supports V3 OOO** with minimal extensions
5. ✅ **Performance overhead minimal** (264 bits storage, ~1ns timing)

### Recommendations

**For V2 Implementation:**
- Store `{sram_base_addr, sram_current_addr}` in each command queue entry
- Initialize both to partition base on queue push
- Increment `sram_current_addr` during W drain
- No additional state tracking needed

**For V3 OOO (Future):**
- Add `draining` flag to command entries
- Implement priority-based command selection (replace FIFO pop)
- Add SRAM data availability checking
- Ensure AWID uniqueness across queue entries

**Alternative Approaches (Not Recommended):**
- ❌ Per-channel pointer array: Fails for multiple commands per channel
- ❌ Separate state table: Redundant with command queue, harder to verify
- ❌ Global pointer with offset calculation: Complex, error-prone

---

## Appendix: Code Snippets

### Complete Command Queue Entry

```systemverilog
typedef struct packed {
    // Channel identification
    logic [3:0]  channel_id;

    // Burst parameters
    logic [7:0]  burst_len;        // Beats in this burst (1-16)

    // SRAM pointer management
    logic [SRAM_ADDR_WIDTH-1:0] sram_base_addr;    // Partition start (constant)
    logic [SRAM_ADDR_WIDTH-1:0] sram_current_addr; // Current position (increments)

    // AXI ID for matching
    logic [ID_WIDTH-1:0] awid;

    // State flags
    logic valid;      // Entry valid
    logic draining;   // Currently being drained (V3 OOO only)
} cmd_queue_entry_t;
```

### SRAM Address Calculation

```systemverilog
// Calculate SRAM base address for channel
function automatic [SRAM_ADDR_WIDTH-1:0] calc_sram_base(input [3:0] ch_id);
    localparam int PARTITION_SIZE = SRAM_DEPTH / NUM_CHANNELS;
    return ch_id * PARTITION_SIZE;
endfunction

// On command queue push
cmd_queue[wr_ptr].sram_base_addr <= calc_sram_base(datawr_channel_id);
cmd_queue[wr_ptr].sram_current_addr <= calc_sram_base(datawr_channel_id);
```

### W Drain SRAM Access

```systemverilog
// Read from current command's SRAM position
assign sram_rd_addr = cmd_queue[rd_ptr].sram_current_addr;
assign sram_rd_en = (drain_state == DRAIN_ACTIVE);

// Increment on W beat transfer
always_ff @(posedge clk) begin
    if (m_axi_wvalid && m_axi_wready) begin
        cmd_queue[rd_ptr].sram_current_addr <=
            cmd_queue[rd_ptr].sram_current_addr + 1'b1;
    end
end
```

---

**Version History:**
- v1.0 (2025-10-28): Initial analysis document
