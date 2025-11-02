# Bridge Transaction CAM Design Proposal

**Date:** 2025-10-26
**Status:** Proposal for Independent Validation
**Priority:** Phase 3A - CAM-Based Transaction Tracking

---

## Executive Summary

This document proposes a specialized CAM module for bridge transaction ID tracking. The design extends the existing `cam_tag.sv` to store transaction metadata (master index) alongside the transaction ID, enabling efficient out-of-order response routing.

**Approach:** Create new `cam_tag_bridge.sv` as a wrapper/extension of existing proven `cam_tag.sv`.

---

## Requirements Analysis

### Current Bridge Implementation (Phase 2)

**Problem:** Uses distributed RAM for ID tracking:
```systemverilog
// Per slave: allocate 2^ID_WIDTH entries regardless of actual usage
logic [$clog2(NUM_MASTERS):0] write_id_table [NUM_SLAVES][2**ID_WIDTH];

// Lookup: O(1) but wastes resources
master_index = write_id_table[slave][bid];  // 256 entries for ID_WIDTH=8!
```

**Issues:**
- ID_WIDTH=8 → 256 entries per slave × NUM_SLAVES (e.g., 4 slaves = 1024 entries)
- Most bridges have <16 outstanding transactions per slave
- **Resource waste:** 94% of entries never used
- No backpressure when ID space exhausted
- No ID reuse detection

### What We Need for Bridge

**Core Functionality:**
1. **Allocate:** Store `{master_index, metadata}` when AW/AR handshake completes
2. **Lookup:** Given transaction ID from B/R response, retrieve master_index
3. **Deallocate:** Free entry when response completes
4. **Status:** `full` flag for backpressure, `empty` for idle detection

**Key Difference from `cam_tag.sv`:**
- `cam_tag.sv`: Only tracks if tag is valid (presence/absence)
- Bridge CAM: Must store and retrieve **associated data** (master_index) with each tag

---

## Proposed Architecture: `cam_tag_bridge.sv`

### Design Option A: Extend `cam_tag` with Data Storage (RECOMMENDED)

**Rationale:** Leverage proven `cam_tag` for tag matching, add parallel data array for payloads.

**Module Interface:**
```systemverilog
module cam_tag_bridge #(
    parameter int TAG_WIDTH = 8,        // Transaction ID width
    parameter int DATA_WIDTH = 8,       // Master index + metadata width
    parameter int DEPTH = 16,           // Outstanding transaction capacity
    parameter int ENABLE = 1            // Global enable
) (
    input  logic                     clk,
    input  logic                     rst_n,

    // === ALLOCATE INTERFACE ===
    // When AW/AR handshake completes
    input  logic                     allocate,
    input  logic [TAG_WIDTH-1:0]     allocate_tag,      // Transaction ID
    input  logic [DATA_WIDTH-1:0]    allocate_data,     // Master index + metadata

    // === LOOKUP INTERFACE ===
    // When B/R response arrives
    input  logic [TAG_WIDTH-1:0]     lookup_tag,        // Transaction ID from response
    output logic                     lookup_valid,       // Tag found in CAM
    output logic [DATA_WIDTH-1:0]    lookup_data,       // Retrieved master index

    // === DEALLOCATE INTERFACE ===
    // When response handshake completes
    input  logic                     deallocate,
    input  logic [TAG_WIDTH-1:0]     deallocate_tag,

    // === STATUS ===
    output logic                     tags_empty,         // No active transactions
    output logic                     tags_full,          // Backpressure needed
    output logic [$clog2(DEPTH):0]   tags_count         // Current occupancy
);
```

### Internal Architecture

**Storage:**
```systemverilog
// Reuse cam_tag for tag matching
logic [TAG_WIDTH-1:0] r_tag_array [DEPTH];
logic [DEPTH-1:0]     r_valid;

// NEW: Parallel data array for master_index storage
logic [DATA_WIDTH-1:0] r_data_array [DEPTH];
```

**Allocation Flow:**
```
1. Check: !tags_full
2. Find: w_next_free_slot (priority encoder, reuse from cam_tag)
3. Store:
   r_tag_array[w_next_free_slot]  <= allocate_tag
   r_data_array[w_next_free_slot] <= allocate_data  // ← NEW
   r_valid[w_next_free_slot]      <= 1'b1
```

**Lookup Flow:**
```
1. Search: Compare lookup_tag against all r_tag_array[*] where r_valid[*]
2. Match: w_match_loc = index of matching entry
3. Retrieve:
   lookup_valid <= (w_match_loc >= 0)
   lookup_data  <= r_data_array[w_match_loc]  // ← NEW
```

**Deallocation Flow:**
```
1. Search: Find matching tag (same as lookup)
2. Clear:
   r_valid[w_match_loc]      <= 1'b0
   r_tag_array[w_match_loc]  <= '0    // Optional: for waveform clarity
   r_data_array[w_match_loc] <= '0    // Optional: for waveform clarity
```

**Occupancy Counter:**
```systemverilog
// NEW: Track number of active entries
logic [$clog2(DEPTH):0] r_count;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        r_count <= '0;
    else begin
        case ({allocate && !tags_full, deallocate && lookup_valid})
            2'b10: r_count <= r_count + 1'b1;  // Alloc only
            2'b01: r_count <= r_count - 1'b1;  // Dealloc only
            default: r_count <= r_count;       // Both or neither
        endcase
    end
end

assign tags_count = r_count;
```

---

## Bridge Integration Example

### Per-Slave CAM Instantiation

**Write Path (AW → B):**
```systemverilog
// One CAM per slave for write transactions
cam_tag_bridge #(
    .TAG_WIDTH(ID_WIDTH),                      // e.g., 8 bits
    .DATA_WIDTH($clog2(NUM_MASTERS)),          // e.g., 2 bits for 4 masters
    .DEPTH(MAX_OUTSTANDING_WRITES_PER_SLAVE)   // e.g., 16 transactions
) u_write_cam [NUM_SLAVES-1:0] (
    .clk(aclk),
    .rst_n(aresetn),

    // Allocate when AW handshake to slave completes
    .allocate(xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]),
    .allocate_tag(xbar_m_axi_awid[s]),
    .allocate_data(aw_granted_master[s]),  // Which master won arbitration

    // Lookup when B response arrives
    .lookup_tag(xbar_m_axi_bid[s]),
    .lookup_valid(b_master_valid[s]),
    .lookup_data(b_master_index[s]),       // Route B to this master

    // Deallocate when B response completes
    .deallocate(xbar_m_axi_bvalid[s] && xbar_m_axi_bready[s]),
    .deallocate_tag(xbar_m_axi_bid[s]),

    // Status for monitoring/backpressure
    .tags_empty(write_cam_empty[s]),
    .tags_full(write_cam_full[s]),
    .tags_count(write_cam_count[s])
);
```

**Read Path (AR → R):**
```systemverilog
// One CAM per slave for read transactions
cam_tag_bridge #(
    .TAG_WIDTH(ID_WIDTH),
    .DATA_WIDTH($clog2(NUM_MASTERS)),
    .DEPTH(MAX_OUTSTANDING_READS_PER_SLAVE)
) u_read_cam [NUM_SLAVES-1:0] (
    .clk(aclk),
    .rst_n(aresetn),

    // Allocate when AR handshake completes
    .allocate(xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]),
    .allocate_tag(xbar_m_axi_arid[s]),
    .allocate_data(ar_granted_master[s]),

    // Lookup when R response arrives
    .lookup_tag(xbar_m_axi_rid[s]),
    .lookup_valid(r_master_valid[s]),
    .lookup_data(r_master_index[s]),

    // Deallocate when R response completes (with RLAST)
    .deallocate(xbar_m_axi_rvalid[s] && xbar_m_axi_rready[s] && xbar_m_axi_rlast[s]),
    .deallocate_tag(xbar_m_axi_rid[s]),

    // Status
    .tags_empty(read_cam_empty[s]),
    .tags_full(read_cam_full[s]),
    .tags_count(read_cam_count[s])
);
```

### Response Routing with CAM

**B Channel Demux:**
```systemverilog
// Route B response to correct master using CAM lookup
always_comb begin
    // Default: no valid responses
    for (int m = 0; m < NUM_MASTERS; m++) begin
        xbar_s_axi_bvalid[m] = 1'b0;
        xbar_s_axi_bid[m] = '0;
        xbar_s_axi_bresp[m] = '0;
    end

    // Demux based on CAM lookup result
    for (int s = 0; s < NUM_SLAVES; s++) begin
        if (xbar_m_axi_bvalid[s] && b_master_valid[s]) begin
            xbar_s_axi_bvalid[b_master_index[s]] = 1'b1;
            xbar_s_axi_bid[b_master_index[s]] = xbar_m_axi_bid[s];
            xbar_s_axi_bresp[b_master_index[s]] = xbar_m_axi_bresp[s];
        end
    end
end
```

**R Channel Demux:** (Similar pattern)

---

## Resource Comparison

### Example: 4x4 Bridge, ID_WIDTH=8

**Current (Distributed RAM):**
- Entries per slave: 2^8 = 256
- Total entries: 256 × 4 slaves × 2 paths (write/read) = **2048 entries**
- Typical usage: ~16 outstanding per slave = **6% utilization**

**With CAM (DEPTH=16):**
- Entries per slave: 16 (configurable)
- Total entries: 16 × 4 slaves × 2 paths = **128 entries**
- Typical usage: ~12-16 outstanding = **75-100% utilization**

**Savings:**
- **16× fewer entries** (2048 → 128)
- **Better resource utilization** (6% → 75%+)
- **Backpressure capability** (prevents ID exhaustion)

---

## Validation Plan

### Phase 1: Standalone CAM Module (CURRENT PROPOSAL)

**Create:** `cam_tag_bridge.sv` in `rtl/common/`
**Test:** `test_cam_tag_bridge.py` in `val/common/`

**Test Scenarios:**
1. **Basic Allocation/Deallocation:**
   - Allocate single entry, lookup, deallocate
   - Verify data retrieval matches stored data

2. **Multiple Outstanding:**
   - Allocate 8 transactions with different IDs and master indices
   - Lookup all 8, verify correct master_index for each
   - Deallocate in random order

3. **Full Condition:**
   - Fill CAM to DEPTH
   - Verify `tags_full` assertion
   - Attempt allocation (should fail gracefully)
   - Deallocate one, verify can allocate again

4. **ID Reuse:**
   - Allocate ID=5, master=0
   - Deallocate ID=5
   - Allocate ID=5, master=2
   - Verify lookup returns master=2 (not stale master=0)

5. **Concurrent Operations:**
   - Allocate and deallocate in same cycle
   - Verify count updates correctly

6. **Lookup Miss:**
   - Lookup non-existent ID
   - Verify `lookup_valid` = 0

**Success Criteria:**
- All tests pass
- 100% code coverage
- No X-propagation in simulation
- Waveform review shows correct behavior

### Phase 2: Bridge Generator Integration

**After** Phase 1 validation complete:
1. Add CAM instantiation to `bridge_response_router.py`
2. Generate test bridge with CAM enabled
3. Verify existing bridge tests still pass
4. Add CAM-specific bridge tests (out-of-order responses)

---

## Implementation Checklist

### Module Creation
- [ ] Create `rtl/common/cam_tag_bridge.sv`
- [ ] Add comprehensive inline documentation
- [ ] Include reset macro usage
- [ ] Add synthesis attributes for FPGA inference

### Testbench Creation
- [ ] Create `val/common/test_cam_tag_bridge.py`
- [ ] Inherit from TBBase
- [ ] Implement all 6 test scenarios above
- [ ] Add parametrized tests for different widths/depths

### Validation
- [ ] Run: `pytest val/common/test_cam_tag_bridge.py -v`
- [ ] Verify 100% test pass rate
- [ ] Lint: `verilator --lint-only rtl/common/cam_tag_bridge.sv`
- [ ] Waveform review for correctness

### Documentation
- [ ] Update `rtl/common/PRD.md` with cam_tag_bridge entry
- [ ] Update `BRIDGE_ARCHITECTURE_ENHANCEMENTS.md` with validation status
- [ ] Create usage examples in module header

### Integration (Phase 3A - FUTURE)
- [ ] Modify `bridge_response_router.py` to instantiate CAMs
- [ ] Add generator parameter: `--enable-cam` (default: false for Phase 2 compatibility)
- [ ] Regenerate bridges with CAM enabled
- [ ] Verify backward compatibility (CAM disabled = current behavior)

---

## Risk Assessment

### Technical Risks

**Risk 1: CAM Area/Timing**
- **Mitigation:** DEPTH parameter allows tuning (start with DEPTH=8, increase if needed)
- **Fallback:** Disable CAM via ENABLE=0 parameter

**Risk 2: Lookup Latency**
- **Impact:** Adds 1 cycle to response path
- **Mitigation:** Acceptable for correctness, can pipeline if needed

**Risk 3: Corner Cases**
- **Mitigation:** Comprehensive test suite catches edge cases before integration

### Integration Risks

**Risk 1: Generator Complexity**
- **Mitigation:** Phased approach (validate CAM standalone first)
- **Fallback:** Keep distributed RAM option via generator flag

**Risk 2: Backward Compatibility**
- **Mitigation:** CAM is opt-in via parameter, existing bridges unchanged

---

## Recommended Next Steps

1. **User Approval:** Review this proposal, provide feedback
2. **Create CAM Module:** Implement `cam_tag_bridge.sv` per spec above
3. **Create Testbench:** Comprehensive `test_cam_tag_bridge.py`
4. **Validate Standalone:** Run tests, achieve 100% pass
5. **Integration:** Only after standalone validation complete

**Estimated Effort:**
- Module creation: 2-3 hours
- Testbench creation: 2-3 hours
- Validation/debugging: 1-2 hours
- **Total: ~6-8 hours** for standalone CAM validation

**Ready to proceed?** If approved, I can create the module and testbench now.

---

**Version:** 1.0
**Author:** Bridge Generator Team
Documentation support by Claude.
