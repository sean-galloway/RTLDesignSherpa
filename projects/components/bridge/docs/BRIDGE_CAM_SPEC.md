# Bridge CAM Specification

**Version:** 1.0
**Date:** 2025-10-26
**Author:** RTL Design Sherpa
**Status:** Production Ready - All Tests Passed

---

## Table of Contents

1. [Overview](#overview)
2. [Purpose and Use Cases](#purpose-and-use-cases)
3. [Operational Modes](#operational-modes)
4. [Interface Description](#interface-description)
5. [Timing Characteristics](#timing-characteristics)
6. [Integration Guide](#integration-guide)
7. [Test Results](#test-results)
8. [Resource Utilization](#resource-utilization)

---

## Overview

The `bridge_cam` module is a Content Addressable Memory (CAM) designed for AXI bridge transaction tracking. It provides fast tag-based lookup for routing response transactions back to the correct master in multi-master bridge crossbars.

### Key Features

- **Two-port design**: Entry port (allocation) and Eviction port (deallocation)
- **Two operational modes**: Simple blocking or FIFO-ordered duplicate handling
- **Fast lookup**: Single-cycle combinational search
- **Optional pipeline**: Timing optimization via configurable eviction pipeline stage
- **FPGA-optimized**: Uses distributed RAM attributes for efficient synthesis
- **Parameterized**: Configurable tag width, data width, and depth

### Critical Design Decisions

**Why Two Ports Instead of Three?**

The initial design considered three ports (Entry, Lookup, Eviction), but this was simplified to two ports:
- **Entry Port**: Used for allocation and implicit lookup (cam_hit signal)
- **Eviction Port**: Used for deallocation with data retrieval

Rationale: In bridge use cases, lookups always occur during allocation (checking for duplicates) or deallocation (retrieving routing data). A separate lookup port would be unused.

**Why Single CAM Search Loop?**

All CAM lookups are performed in a single `always_comb` block that generates match vectors:
- `w_entry_matches[DEPTH]` - Matches for Entry port (allocate_tag)
- `w_evict_matches[DEPTH]` - Matches for Eviction port (deallocate_tag)

Subsequent logic operates only on matched entries, significantly reducing timing paths.

---

## Purpose and Use Cases

### Primary Use Case: AXI Bridge Transaction Tracking

In multi-master AXI bridge crossbars, response transactions (B and R channels) must be routed back to the originating master. The bridge_cam provides this routing by:

1. **Allocation**: When a master issues a request (AW or AR), store the transaction ID with the master index
2. **Lookup**: When a slave returns a response (B or R), look up the transaction ID
3. **Deallocation**: Retrieve the master index and free the CAM entry

### Mode 1: Simple Bridges (ALLOW_DUPLICATES=0)

**Use Case**: Bridges where masters never reuse transaction IDs until responses complete.

**Behavior**:
- Allocation with duplicate ID asserts `cam_hit` (duplicate detected)
- External arbiter blocks the transaction
- Prevents same ID from being allocated twice
- Simple, deterministic routing

**Example**: Single-threaded masters, in-order slave responses

### Mode 2: Out-of-Order Slave Support (ALLOW_DUPLICATES=1)

**Use Case**: Bridges where slave responses may complete out-of-order, requiring FIFO ordering of duplicate IDs.

**Behavior**:
- Allows duplicate transaction IDs with count field for ordering
- First allocation: count=0 (oldest)
- Subsequent allocations: count incremented (1, 2, 3...)
- Deallocation always frees count=0 entry first (FIFO)
- Remaining entries have counts decremented

**Example**: Multi-threaded masters with out-of-order DRAM controllers

### When to Use Each Mode

| Scenario | Mode | Reason |
|----------|------|--------|
| In-order slaves | Mode 1 | Simpler logic, no count overhead |
| Out-of-order slaves | Mode 2 | FIFO ordering ensures correct master routing |
| Single master | Either | Duplicate IDs unlikely |
| Multi-master | Mode 1 or 2 | Depends on slave characteristics |
| DRAM controllers | Mode 2 | Out-of-order responses common |
| SRAM/peripherals | Mode 1 | Typically in-order |

---

## Operational Modes

### Mode 1: Simple Blocking (ALLOW_DUPLICATES=0)

**Allocation:**
```
IF cam_hit == 1 THEN
    Block transaction (external arbiter decision)
ELSE
    Allocate entry at next free slot
    Store: tag → data (master_index)
END IF
```

**Deallocation:**
```
Search for matching tag
IF found THEN
    Return data (master_index)
    Free entry
ELSE
    No operation (deallocate_valid = 0)
END IF
```

**Status:**
- `cam_hit`: Asserted if allocate_tag exists in CAM
- `tags_full`: Asserted when r_count == DEPTH (physical capacity)
- `tags_empty`: Asserted when r_count == 0

### Mode 2: FIFO Ordering (ALLOW_DUPLICATES=1)

**Allocation:**
```
IF cam_hit == 1 THEN
    Find max count for this tag
    Allocate new entry with count = max_count + 1
ELSE
    Allocate new entry with count = 0
END IF
```

**Deallocation:**
```
Search for matching tag with count == 0
IF found THEN
    Return data for count=0 entry
    Free count=0 entry
    Decrement count for all other matching entries
ELSE
    No operation (deallocate_valid = 0)
END IF
```

**FIFO Ordering Example:**

```
Time  Action                     CAM State
----  -------------------------  ------------------------------------------
T0    Allocate(tag=0x5, data=A)  Entry0: tag=0x5, data=A, count=0
T1    Allocate(tag=0x5, data=B)  Entry0: tag=0x5, data=A, count=0
                                  Entry1: tag=0x5, data=B, count=1
T2    Allocate(tag=0x5, data=C)  Entry0: tag=0x5, data=A, count=0
                                  Entry1: tag=0x5, data=B, count=1
                                  Entry2: tag=0x5, data=C, count=2
T3    Deallocate(tag=0x5)        Returns: data=A (count was 0)
                                  Entry1: tag=0x5, data=B, count=0 (decremented)
                                  Entry2: tag=0x5, data=C, count=1 (decremented)
T4    Deallocate(tag=0x5)        Returns: data=B (count was 0)
                                  Entry2: tag=0x5, data=C, count=0 (decremented)
T5    Deallocate(tag=0x5)        Returns: data=C (count was 0)
                                  CAM empty
```

**Status:**
- `cam_hit`: Always reports if tag exists (policy decision is external)
- `tags_full`: Asserted when r_count == DEPTH (physical capacity only)
- `tags_empty`: Asserted when r_count == 0

---

## Interface Description

### Module Parameters

```systemverilog
module bridge_cam #(
    parameter int TAG_WIDTH = 8,           // Transaction ID width
    parameter int DATA_WIDTH = 8,          // Master index width
    parameter int DEPTH = 16,              // Number of CAM entries
    parameter int ALLOW_DUPLICATES = 0,    // 0=Mode 1, 1=Mode 2
    parameter int PIPELINE_EVICT = 0       // 0=Comb, 1=Pipelined
);
```

| Parameter | Description | Typical Values | Constraints |
|-----------|-------------|----------------|-------------|
| `TAG_WIDTH` | Transaction ID bit width | 4, 8, 12 | Must match AXI ID_WIDTH |
| `DATA_WIDTH` | Master index bit width | 4, 8 | $clog2(NUM_MASTERS) |
| `DEPTH` | Number of CAM entries | 8, 16, 32 | Power of 2 recommended |
| `ALLOW_DUPLICATES` | Mode selection | 0 or 1 | 0=Mode 1, 1=Mode 2 |
| `PIPELINE_EVICT` | Eviction pipeline | 0 or 1 | Use 1 for timing closure |

### Port Definitions

#### Clock and Reset

```systemverilog
input  logic                    clk,
input  logic                    rst_n,
```

- `clk`: System clock (all operations synchronous)
- `rst_n`: Active-low asynchronous reset

#### Entry Port (Allocation)

```systemverilog
input  logic                    allocate,
input  logic [TAG_WIDTH-1:0]    allocate_tag,
input  logic [DATA_WIDTH-1:0]   allocate_data,
```

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `allocate` | Input | 1 | Enable signal for allocation |
| `allocate_tag` | Input | TAG_WIDTH | Transaction ID to store |
| `allocate_data` | Input | DATA_WIDTH | Associated data (master_index) |

**Timing**: Allocation occurs on rising edge of clk when allocate=1.

#### Eviction Port (Deallocation)

```systemverilog
input  logic                        deallocate,
input  logic [TAG_WIDTH-1:0]        deallocate_tag,
output logic                        deallocate_valid,
output logic [DATA_WIDTH-1:0]       deallocate_data,
output logic [$clog2(DEPTH):0]      deallocate_count,
```

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `deallocate` | Input | 1 | Enable signal for deallocation |
| `deallocate_tag` | Input | TAG_WIDTH | Transaction ID to free |
| `deallocate_valid` | Output | 1 | Tag found and freed |
| `deallocate_data` | Output | DATA_WIDTH | Retrieved data (master_index) |
| `deallocate_count` | Output | $clog2(DEPTH)+1 | Ordering counter (Mode 2 only) |

**Timing**:
- **PIPELINE_EVICT=0**: Outputs are combinational (valid same cycle)
- **PIPELINE_EVICT=1**: Outputs are registered (+1 cycle latency)

#### Status Outputs

```systemverilog
output logic                    cam_hit,
output logic                    tags_empty,
output logic                    tags_full,
output logic [$clog2(DEPTH):0]  tags_count
```

| Signal | Width | Description | When Asserted |
|--------|-------|-------------|---------------|
| `cam_hit` | 1 | Tag exists in CAM | allocate_tag found (both modes) |
| `tags_empty` | 1 | No active entries | tags_count == 0 |
| `tags_full` | 1 | Physical capacity reached | tags_count == DEPTH |
| `tags_count` | $clog2(DEPTH)+1 | Current occupancy | 0 to DEPTH |

---

## Timing Characteristics

### Allocation Timing (Both Modes)

```
Cycle:     N         N+1
           |         |
clk:    ___/‾‾‾\___/‾‾‾\___
           |         |
allocate: ‾‾‾‾‾‾‾‾‾\________
allocate_tag: <TAG>
allocate_data: <DATA>
           |         |
cam_hit:   X    <HIT?>    (combinational)
tags_full: X    <FULL?>   (combinational)
           |         |
           | Storage |
           | occurs  |
```

- **Cycle N**: Drive allocate, allocate_tag, allocate_data
- **Cycle N (comb)**: cam_hit and tags_full update combinationally
- **Cycle N→N+1**: Storage occurs on rising edge if not full

### Deallocation Timing - Combinational (PIPELINE_EVICT=0)

```
Cycle:     N
           |
clk:    ___/‾‾‾\___
           |
deallocate: ‾‾‾‾‾‾‾‾‾\________
deallocate_tag: <TAG>
           |
deallocate_valid: X <VALID?> (combinational)
deallocate_data:  X <DATA>   (combinational)
           |
           | Deallocation
           | occurs
```

- **Cycle N**: Drive deallocate, deallocate_tag
- **Cycle N (comb)**: deallocate_valid and deallocate_data available **same cycle**
- **Cycle N→N+1**: Internal state updated on rising edge

### Deallocation Timing - Pipelined (PIPELINE_EVICT=1)

```
Cycle:     N         N+1       N+2
           |         |         |
clk:    ___/‾‾‾\___/‾‾‾\___/‾‾‾\___
           |         |         |
deallocate: ‾‾‾‾‾‾‾‾‾\________________
deallocate_tag: <TAG>
           |         |         |
deallocate_valid: X         <VALID?> (registered)
deallocate_data:  X         <DATA>   (registered)
           |         |         |
           | Pipeline| Dealloc |
           | stage   | occurs  |
```

- **Cycle N**: Drive deallocate, deallocate_tag
- **Cycle N+1**: Pipeline stage (match vector registered)
- **Cycle N+1 (comb)**: deallocate_valid and deallocate_data available
- **Cycle N+1→N+2**: Internal state updated on rising edge

**Use PIPELINE_EVICT=1 when:**
- Critical timing paths fail to meet timing
- Complex deallocation logic (Mode 2 with large DEPTH)
- Can tolerate +1 cycle latency for responses

### Simultaneous Allocation and Deallocation

Allocation and deallocation can occur **simultaneously in the same cycle**:

```
Cycle:     N         N+1
           |         |
clk:    ___/‾‾‾\___/‾‾‾\___
           |         |
allocate: ‾‾‾‾‾‾‾‾‾\________
deallocate: ‾‾‾‾‾‾‾‾‾\________
           |         |
tags_count: <N>   <N>       (unchanged if both succeed)
```

Independent operations:
- Allocation: Writes to free slot
- Deallocation: Frees occupied slot
- Net change in occupancy: +1 -1 = 0 (if both succeed)

---

## Integration Guide

### Step 1: Determine Configuration

**Questions to answer:**

1. **How many masters?** → Sets DATA_WIDTH = $clog2(NUM_MASTERS)
2. **What is AXI ID width?** → Sets TAG_WIDTH = ID_WIDTH
3. **Max outstanding transactions?** → Sets DEPTH (recommend 2x expected)
4. **Do slaves respond out-of-order?** → Sets ALLOW_DUPLICATES (1=yes, 0=no)
5. **Timing critical?** → Sets PIPELINE_EVICT (1=yes, 0=no)

**Example**: 4-master bridge, 8-bit IDs, 16 max outstanding, out-of-order slaves
```systemverilog
bridge_cam #(
    .TAG_WIDTH(8),          // Matches AXI ID_WIDTH
    .DATA_WIDTH(2),         // $clog2(4 masters) = 2
    .DEPTH(16),             // 16 outstanding transactions
    .ALLOW_DUPLICATES(1),   // Out-of-order slave support
    .PIPELINE_EVICT(0)      // Start with combinational
) u_bridge_cam (
    .clk(aclk),
    .rst_n(aresetn),
    // ...
);
```

### Step 2: Connect to AXI Bridge Write Path

**Allocation**: When master issues AW transaction and arbiter grants access

```systemverilog
// Write address channel - allocate on grant
assign cam_allocate = s_axi_awvalid & s_axi_awready & grant;
assign cam_allocate_tag = s_axi_awid;
assign cam_allocate_data = master_index;  // From arbiter

// Check for duplicates (Mode 1 only)
if (ALLOW_DUPLICATES == 0) begin
    // Block allocation if cam_hit asserts
    assign grant = arbiter_grant & !cam_hit;
end
```

**Deallocation**: When slave returns B response

```systemverilog
// Write response channel - deallocate on valid
assign cam_deallocate = m_axi_bvalid & m_axi_bready;
assign cam_deallocate_tag = m_axi_bid;

// Route response to correct master
assign master_select = cam_deallocate_data;  // From CAM lookup
assign s_axi_bvalid[master_select] = cam_deallocate_valid & m_axi_bvalid;
```

### Step 3: Connect to AXI Bridge Read Path

**Allocation**: When master issues AR transaction and arbiter grants access

```systemverilog
// Read address channel - allocate on grant
assign cam_allocate = s_axi_arvalid & s_axi_arready & grant;
assign cam_allocate_tag = s_axi_arid;
assign cam_allocate_data = master_index;  // From arbiter
```

**Deallocation**: When slave returns R response (on RLAST)

```systemverilog
// Read data channel - deallocate on RLAST
assign cam_deallocate = m_axi_rvalid & m_axi_rready & m_axi_rlast;
assign cam_deallocate_tag = m_axi_rid;

// Route response to correct master
assign master_select = cam_deallocate_data;  // From CAM lookup
assign s_axi_rvalid[master_select] = cam_deallocate_valid & m_axi_rvalid;
```

### Step 4: Handle Edge Cases

**CAM Full Condition:**

```systemverilog
// Option 1: Block new transactions (backpressure)
assign s_axi_awready = !tags_full & /* other ready conditions */;
assign s_axi_arready = !tags_full & /* other ready conditions */;

// Option 2: Allow transaction but log error
always_ff @(posedge clk) begin
    if (allocate && tags_full) begin
        $error("CAM overflow - transaction dropped");
    end
end
```

**Invalid Deallocation (Tag Not Found):**

```systemverilog
// Monitor for missing tags
always_ff @(posedge clk) begin
    if (deallocate && !deallocate_valid) begin
        $warning("Deallocate failed - tag 0x%0h not found", deallocate_tag);
    end
end
```

**Reset Handling:**

```systemverilog
// CAM self-clears on reset
// No additional initialization required
```

### Step 5: Verification Checklist

- [ ] Verify TAG_WIDTH matches AXI ID_WIDTH
- [ ] Verify DATA_WIDTH can encode all masters: 2^DATA_WIDTH >= NUM_MASTERS
- [ ] Verify DEPTH accommodates expected outstanding transactions
- [ ] Test with CAM full condition (backpressure)
- [ ] Test with invalid deallocations (missing tags)
- [ ] For Mode 2: Verify FIFO ordering with out-of-order slave responses
- [ ] Run with assertions enabled to catch protocol violations

---

## Test Results

### Test Coverage Summary

**Test Levels:**
- GATE: Minimal configurations (quick smoke test)
- FUNC: Medium configurations (typical use cases)
- FULL: Comprehensive configurations (all corner cases)

### FULL Level Results (8 configurations, all passed)

| Configuration | Mode | TAG_WIDTH | DATA_WIDTH | DEPTH | Result | Notes |
|---------------|------|-----------|------------|-------|--------|-------|
| Config 1 | Mode 1 | 8 | 8 | 16 | PASS | Standard size |
| Config 2 | Mode 2 | 8 | 8 | 16 | PASS | Standard size, FIFO |
| Config 3 | Mode 1 | 4 | 4 | 8 | PASS | Small size |
| Config 4 | Mode 2 | 4 | 4 | 8 | PASS | Small size, FIFO |
| Config 5 | Mode 1 | 8 | 8 | 32 | PASS | Large depth |
| Config 6 | Mode 2 | 8 | 8 | 32 | PASS | Large depth, FIFO |
| Config 7 | Mode 1 | 12 | 12 | 16 | PASS | Wide tags/data |
| Config 8 | Mode 2 | 12 | 12 | 16 | PASS | Wide tags/data, FIFO |

**Total: 8/8 configurations passed (100% success rate)**

### Test Phases (Each Configuration)

1. **Basic CAM Test**
   - Allocate entry with known tag/data
   - Verify cam_hit behavior
   - Deallocate and verify data retrieval
   - Check empty/full status flags

2. **Capacity Test**
   - Fill CAM to DEPTH entries
   - Verify tags_full assertion
   - Attempt overflow allocation
   - Remove all entries
   - Verify tags_empty assertion

3. **Mode 2 FIFO Test** (ALLOW_DUPLICATES=1 only)
   - Allocate same tag three times with different data
   - Verify count field increments (0, 1, 2)
   - Deallocate three times
   - Verify FIFO ordering (data returned in order 0, 1, 2)

### Bugs Found and Fixed

**No functional RTL bugs found!** All issues were synthesis warnings or testbench problems:

1. **MULTIDRIVEN Warning**: Fixed by using unique iterator variables
2. **WIDTHEXPAND Warning**: Fixed by adding explicit width cast
3. **Testbench timing issue**: Fixed ReadOnly() trigger for combinational outputs
4. **Testbench overflow**: Fixed hardcoded values to use max_tag/max_data

### Verification Tools

- **Simulator**: Verilator 5.028
- **Testbench Framework**: CocoTB
- **Coverage**: Functional coverage via test phases
- **Assertions**: Built-in assertions in testbench

---

## Resource Utilization

### FPGA Synthesis

**Xilinx Targeting:**
```systemverilog
(* ram_style = "distributed" *)
```

**Intel Targeting:**
```systemverilog
/* synthesis ramstyle = "MLAB" */
```

### Estimated Resources (Xilinx 7-Series)

**Configuration: TAG_WIDTH=8, DATA_WIDTH=8, DEPTH=16, ALLOW_DUPLICATES=0**

| Resource | Estimated Count | Notes |
|----------|----------------|-------|
| LUTs | ~150 | CAM search logic + muxing |
| Flip-Flops | ~290 | Tag/data arrays + valid bits + count |
| Distributed RAM | 32 LUTs | Tag array (16 entries x 8 bits) |
| Distributed RAM | 32 LUTs | Data array (16 entries x 8 bits) |

**Configuration: TAG_WIDTH=8, DATA_WIDTH=8, DEPTH=16, ALLOW_DUPLICATES=1**

| Resource | Estimated Count | Notes |
|----------|----------------|-------|
| LUTs | ~220 | Additional count logic + decrement |
| Flip-Flops | ~370 | Add count array (16 entries x 5 bits) |
| Distributed RAM | 80 LUTs | Tag + data + count arrays |

### Scaling with Parameters

**LUT scaling** (approximate):
- Base logic: ~50 LUTs
- CAM search: ~5 LUTs per DEPTH entry
- Mode 2 overhead: +50% LUTs (count logic)

**Flip-Flop scaling**:
- FF count ≈ DEPTH * (TAG_WIDTH + DATA_WIDTH + 1)
- Mode 2 adds: DEPTH * $clog2(DEPTH)

**Timing**:
- Critical path: CAM search → priority encoder → mux
- Scales logarithmically with DEPTH
- Use PIPELINE_EVICT=1 for DEPTH > 32

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-26 | RTL Design Sherpa | Initial release, all tests passed |

---

## References

1. `projects/components/bridge/rtl/bridge_cam.sv` - RTL source code
2. `projects/components/bridge/dv/tbclasses/bridge_cam_tb.py` - Testbench class
3. `projects/components/bridge/dv/tests/test_bridge_cam.py` - Test runner
4. `projects/components/bridge/CLAUDE.md` - Integration guidelines
5. AXI4 Specification (ARM IHI 0022E)
