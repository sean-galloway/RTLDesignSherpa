# V2 AXI Engine Implementation Plan

**Status:** IN PROGRESS
**Started:** 2025-10-28
**Target Completion:** Accelerated timeline (1-2 weeks)

---

## Overview

Implementing V2 command pipelined architecture for AXI read and write engines to achieve 6.7x throughput improvement over V1.

---

## Implementation Strategy

### Approach: Conditional Compilation with Runtime Parameters

**NOT using generate blocks** (complexity, synthesis issues)
**USING runtime conditional logic** with parameter-based enable

**Rationale:**
- Simpler code structure
- Easier debugging
- Better synthesis optimization
- V1 logic remains untouched when `ENABLE_CMD_PIPELINE = 0`

---

## Phase 1: Read Engine V2 (CURRENT)

### Step 1.1: Add Parameters ✅ COMPLETE

**Files Modified:** `axi_read_engine.sv`

**Changes:**
```systemverilog
parameter bit ENABLE_CMD_PIPELINE = 0,    // 0=V1 (default), 1=V2
parameter int CMD_QUEUE_DEPTH = 4,        // Command queue depth
parameter int MAX_OUTSTANDING = 4         // Max outstanding transactions
```

### Step 1.2: Add V2 Data Structures ✅ COMPLETE

**Added:**
- `read_cmd_queue_entry_t` typedef
- Command queue array `cmd_queue [CMD_QUEUE_DEPTH]`
- Queue pointers: `cmd_wr_ptr`, `cmd_rd_ptr`, `cmd_count`
- Outstanding transaction counter
- Transaction ID counter

### Step 1.3: Modify AR Channel Logic ✅ COMPLETE

**Changes Needed:**

1. **datard_ready signal:**
```systemverilog
// V1: Single outstanding
assign datard_ready_v1 = !r_ar_inflight && !r_ar_valid;

// V2: Command queue space available
assign datard_ready_v2 = (cmd_count < CMD_QUEUE_DEPTH) &&
                          (outstanding_reads < MAX_OUTSTANDING);

// Select based on parameter
assign datard_ready = ENABLE_CMD_PIPELINE ? datard_ready_v2 : datard_ready_v1;
```

2. **Request acceptance:**
```systemverilog
if (ENABLE_CMD_PIPELINE) begin
    // V2: Push to command queue
    if (datard_valid && datard_ready) begin
        cmd_queue[cmd_wr_ptr].channel_id <= datard_channel_id;
        cmd_queue[cmd_wr_ptr].burst_len <= w_capped_burst_len;
        cmd_queue[cmd_wr_ptr].sram_base_addr <= calc_sram_base(datard_channel_id);
        cmd_queue[cmd_wr_ptr].sram_current_addr <= calc_sram_base(datard_channel_id);
        cmd_queue[cmd_wr_ptr].arid <= {transaction_counter, datard_channel_id};
        cmd_queue[cmd_wr_ptr].valid <= 1'b1;

        cmd_wr_ptr <= cmd_wr_ptr + 1'b1;
        cmd_count <= cmd_count + 1'b1;
    end
end else begin
    // V1: Direct to AR registers (existing logic)
    if (datard_valid && datard_ready) begin
        r_ar_addr <= datard_addr;
        r_ar_len <= w_capped_burst_len;
        r_ar_channel_id <= datard_channel_id;
        r_ar_valid <= 1'b1;
        r_ar_inflight <= 1'b1;
    end
end
```

3. **AR channel outputs:**
```systemverilog
// V2: From command queue head
assign m_axi_arid_v2 = cmd_queue[cmd_rd_ptr].arid;
assign m_axi_araddr_v2 = /* need to track address in queue */;
assign m_axi_arlen_v2 = cmd_queue[cmd_rd_ptr].burst_len;

// V1: From registers
assign m_axi_arid_v1 = {4'h0, r_ar_channel_id};
assign m_axi_araddr_v1 = r_ar_addr;
assign m_axi_arlen_v1 = r_ar_len;

// Select
assign m_axi_arid = ENABLE_CMD_PIPELINE ? m_axi_arid_v2 : m_axi_arid_v1;
assign m_axi_araddr = ENABLE_CMD_PIPELINE ? m_axi_araddr_v2 : m_axi_araddr_v1;
assign m_axi_arlen = ENABLE_CMD_PIPELINE ? m_axi_arlen_v2 : m_axi_arlen_v1;
```

### Step 1.4: Modify R Channel Logic ✅ COMPLETE

**Changes Needed:**

1. **SRAM write address:**
```systemverilog
// V2: From command queue (per-command pointer)
assign sram_wr_addr_v2 = cmd_queue[cmd_rd_ptr].sram_current_addr;

// V1: From single pointer
assign sram_wr_addr_v1 = r_sram_wr_ptr;

// Select
assign sram_wr_addr = ENABLE_CMD_PIPELINE ? sram_wr_addr_v2 : sram_wr_addr_v1;
```

2. **Pointer updates:**
```systemverilog
if (ENABLE_CMD_PIPELINE) begin
    // V2: Update queue entry pointer
    if (m_axi_rvalid && m_axi_rready) begin
        cmd_queue[cmd_rd_ptr].sram_current_addr <=
            cmd_queue[cmd_rd_ptr].sram_current_addr + 1'b1;

        // Pop queue on rlast
        if (m_axi_rlast) begin
            cmd_rd_ptr <= cmd_rd_ptr + 1'b1;
            cmd_count <= cmd_count - 1'b1;
        end
    end
end else begin
    // V1: Update single pointer (existing logic)
    if (m_axi_rvalid && m_axi_rready) begin
        r_sram_wr_ptr <= r_sram_wr_ptr + 1'b1;
        if (r_sram_wr_ptr == SRAM_ADDR_WIDTH'(SRAM_DEPTH - 1)) begin
            r_sram_wr_ptr <= '0;
        end
    end
end
```

### Step 1.5: Helper Function - SRAM Base Address Calculation

**Need to add:**
```systemverilog
function automatic logic [SRAM_ADDR_WIDTH-1:0] calc_sram_base(input logic [3:0] channel_id);
    // Per-channel SRAM partitioning
    // Assumes 8 channels, SRAM_DEPTH = 4096
    // Each channel gets SRAM_DEPTH / 8 = 512 entries
    localparam int PARTITION_SIZE = SRAM_DEPTH / 8;
    return channel_id * PARTITION_SIZE;
endfunction
```

---

## Phase 2: Write Engine V2 (NEXT)

### Similar to Read Engine, Plus:

1. **W Drain FSM** (3 states: IDLE, ACTIVE, WAIT)
2. **B Response Scoreboard** (async tracking)
3. **SRAM read pointer** per-command

**Additional Complexity:**
- W channel decoupled from AW (drain from SRAM)
- B responses asynchronous (scoreboard needed)

---

## Phase 3: Testing (CONCURRENT)

### V1 Regression
- Ensure existing tests still pass with `ENABLE_CMD_PIPELINE = 0`

### V2 Validation
- Create `test_axi_read_engine_v2.py`
- Test command queue functionality
- Test multiple outstanding transactions
- Test per-command SRAM pointers

### V1 vs V2 Comparison
- Create `test_axi_engines_v1_v2_comparison.py`
- Measure throughput improvement
- Validate 6.7x target

---

## Implementation Checklist

### Read Engine V2
- [x] Add V2 parameters
- [x] Add command queue structure
- [x] Add V2 signals
- [x] Add calc_sram_base() function
- [x] Modify datard_ready logic (V1/V2 select)
- [x] Modify AR channel (V1/V2 paths)
- [x] Modify R channel (V1/V2 paths)
- [x] Add command queue management logic
- [x] Add outstanding transaction tracking
- [x] Test V1 mode still works (PASSED: test_datapath_rd_basic)
- [ ] Test V2 mode functional

### Write Engine V2
- [ ] Add V2 parameters
- [ ] Add command queue structure
- [ ] Add W drain FSM
- [ ] Add B scoreboard
- [ ] Modify datawr_ready logic
- [ ] Modify AW channel
- [ ] Modify W channel (drain FSM)
- [ ] Modify B channel (scoreboard)
- [ ] Test V1 mode still works
- [ ] Test V2 mode functional

### Testing
- [ ] V1 regression (13/13 tests PASS)
- [ ] V2 read engine tests
- [ ] V2 write engine tests
- [ ] V1 vs V2 performance comparison
- [ ] Document results

---

## Accelerated Timeline

**Week 1 (Days 1-3):**
- Complete read engine V2 logic
- Create V2 read tests
- Validate V2 read functionality

**Week 1 (Days 4-7):**
- Complete write engine V2 logic
- Create V2 write tests
- V1 regression testing

**Week 2 (Days 1-4):**
- Performance benchmarking
- Bug fixes and optimization
- Documentation updates

**Week 2 (Days 5-7):**
- Final validation
- Performance comparison report
- Release V2 implementation

---

## Risk Mitigation

**Risk:** Breaking V1 functionality
**Mitigation:** Run V1 tests after every change

**Risk:** Synthesis issues with conditionals
**Mitigation:** Small incremental changes, lint after each

**Risk:** SRAM pointer collisions
**Mitigation:** Per-channel partitioning, validated in tests

**Risk:** Command queue deadlock
**Mitigation:** Careful ready/valid handshaking, full/empty flags

---

**Last Updated:** 2025-10-28
**Next Milestone:** Complete read engine V2 AR/R channel logic
