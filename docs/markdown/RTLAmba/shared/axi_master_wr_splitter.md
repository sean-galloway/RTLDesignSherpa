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

# AXI Master Write Splitter

**Module:** `axi_master_wr_splitter.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI Master Write Splitter handles the complex task of splitting boundary-crossing write transactions while maintaining data integrity and response consolidation. Unlike read splitting which simply passes through responses, write splitting must aggregate multiple split responses into a single consolidated response with proper error priority handling.

### Key Features

- Automatic boundary crossing detection for write transactions
- AW + W channel forwarding with synchronized address/data flow
- B channel response consolidation (N responses → 1 consolidated response)
- Error priority handling (DECERR > SLVERR > EXOKAY > OKAY)
- WLAST regeneration for split boundaries
- Zero added latency for non-split transactions
- Full AXI4 protocol compliance with user extensions

---

## Module Purpose

Write transaction splitting presents unique challenges compared to read splitting due to the tight coupling between address (AW), data (W), and response (B) channels. The AXI Master Write Splitter solves these challenges while maintaining protocol correctness.

**Problem Statement:**
- Upstream master issues write (ADDR=0x0FC0, LEN=7, 8 data beats)
- Transaction crosses 4KB boundary at 0x1000
- Downstream requires separate transactions per boundary
- Each split generates independent response
- Upstream expects single consolidated response

**Solution:**
- Module detects boundary crossing using combinational split logic
- AW channel: Generates N split address transactions
- W channel: Regenerates WLAST at split boundaries
- B channel: Consolidates N responses into 1 (error priority)
- Example split:
  - Split 1: ADDR=0x0FC0, LEN=0 (1 beat) → Response: OKAY
  - Split 2: ADDR=0x1000, LEN=6 (7 beats) → Response: OKAY
  - Consolidated: OKAY (worst error across all splits)

**Key Invariants:**
- Upstream sees exactly ONE write transaction with ONE response
- Downstream sees N split transactions with N responses
- Consolidated response reflects worst error status
- Write data flows through unchanged (WLAST regenerated)
- All AXI signaling preserved across splits

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | Width of AXI ID signals (AWID, BID) |
| AXI_ADDR_WIDTH | int | 32 | Width of AXI address bus (AWADDR) |
| AXI_DATA_WIDTH | int | 32 | Width of AXI data bus (WDATA), must be power of 2 (32-1024 bits) |
| AXI_USER_WIDTH | int | 1 | Width of AXI user extension fields (AWUSER, WUSER, BUSER) |
| SPLIT_FIFO_DEPTH | int | 4 | Depth of split information tracking FIFO |
| IW | int | AXI_ID_WIDTH | Shorthand alias for ID width |
| AW | int | AXI_ADDR_WIDTH | Shorthand alias for address width |
| DW | int | AXI_DATA_WIDTH | Shorthand alias for data width |
| UW | int | AXI_USER_WIDTH | Shorthand alias for user width |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Global clock for all AXI interfaces |
| aresetn | input | 1 | Active-low asynchronous reset |

### Configuration Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| alignment_mask | input | 12 | 12-bit boundary alignment mask (e.g., 0xFFF for 4KB boundaries) |
| block_ready | input | 1 | Backpressure from error monitor (suppresses fub_awready when asserted) |

### Master AXI Write Interface (Downstream)

**AW Channel (Address Write):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_awid | output | IW | Transaction ID for split write transactions |
| m_axi_awaddr | output | AW | Calculated address for current split (boundary-aligned) |
| m_axi_awlen | output | 8 | Calculated burst length for current split (AXI encoding: beats-1) |
| m_axi_awsize | output | 3 | Transfer size (preserved from original transaction) |
| m_axi_awburst | output | 2 | Burst type (preserved from original, typically INCR) |
| m_axi_awlock | output | 1 | Lock type (preserved from original) |
| m_axi_awcache | output | 4 | Cache attributes (preserved from original) |
| m_axi_awprot | output | 3 | Protection attributes (preserved from original) |
| m_axi_awqos | output | 4 | Quality of Service (preserved from original) |
| m_axi_awregion | output | 4 | Region identifier (preserved from original) |
| m_axi_awuser | output | UW | User-defined extension (preserved from original) |
| m_axi_awvalid | output | 1 | Valid signal for current split transaction |
| m_axi_awready | input | 1 | Ready signal from downstream slave |

**W Channel (Write Data):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_wdata | output | DW | Write data payload (pass-through from fub) |
| m_axi_wstrb | output | DW/8 | Write strobes (pass-through from fub) |
| m_axi_wlast | output | 1 | Last beat indicator (regenerated at split boundaries) |
| m_axi_wuser | output | UW | User-defined extension (pass-through from fub) |
| m_axi_wvalid | output | 1 | Valid signal for write data (pass-through from fub) |
| m_axi_wready | input | 1 | Ready signal from downstream slave |

**B Channel (Write Response):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_bid | input | IW | Response transaction ID (matches AWID) |
| m_axi_bresp | input | 2 | Response status (OKAY=00, EXOKAY=01, SLVERR=10, DECERR=11) |
| m_axi_buser | input | UW | User-defined extension for response |
| m_axi_bvalid | input | 1 | Valid signal for response |
| m_axi_bready | output | 1 | Ready signal to downstream slave (controlled during consolidation) |

### Slave AXI Write Interface (Upstream / FUB)

**AW Channel (Address Write):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_awid | input | IW | Original transaction ID from upstream master |
| fub_awaddr | input | AW | Original starting address (may cross boundaries) |
| fub_awlen | input | 8 | Original burst length (may span multiple boundaries) |
| fub_awsize | input | 3 | Transfer size per beat |
| fub_awburst | input | 2 | Burst type (FIXED, INCR, WRAP) |
| fub_awlock | input | 1 | Lock type for atomic operations |
| fub_awcache | input | 4 | Cache attributes |
| fub_awprot | input | 3 | Protection attributes |
| fub_awqos | input | 4 | Quality of Service priority |
| fub_awregion | input | 4 | Region identifier |
| fub_awuser | input | UW | User-defined extension |
| fub_awvalid | input | 1 | Valid signal for original transaction |
| fub_awready | output | 1 | Ready signal to upstream master (suppressed until all splits complete) |

**W Channel (Write Data):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_wdata | input | DW | Write data payload from upstream master |
| fub_wstrb | input | DW/8 | Write strobes from upstream master |
| fub_wlast | input | 1 | Last beat indicator from upstream master |
| fub_wuser | input | UW | User-defined extension |
| fub_wvalid | input | 1 | Valid signal for write data |
| fub_wready | output | 1 | Ready signal to upstream master (pass-through from m_axi) |

**B Channel (Write Response):**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_bid | output | IW | Consolidated response transaction ID (original AWID) |
| fub_bresp | output | 2 | Consolidated response status (worst error across all splits) |
| fub_buser | output | UW | User-defined extension (from original transaction) |
| fub_bvalid | output | 1 | Valid signal for consolidated response (only after all splits received) |
| fub_bready | input | 1 | Ready signal from upstream master |

### Split Information Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_split_addr | output | AW | Original transaction starting address |
| fub_split_id | output | IW | Original transaction ID |
| fub_split_cnt | output | 8 | Number of split transactions generated (2+ if split occurred) |
| fub_split_valid | output | 1 | Valid signal for split information |
| fub_split_ready | input | 1 | Ready signal from split information consumer |

---

## Functional Description

### Write Transaction Splitting Overview

Write splitting requires coordinated management of three independent AXI channels with different timing characteristics.

**Non-Split Path (Fast):**
- Transaction fully contained within single boundary
- AW/W signals pass directly from fub to m_axi
- fub_awready = m_axi_awready (immediate acceptance)
- B channel passes through directly
- Split count = 1

**Split Path (Multi-Transaction + Response Consolidation):**
- Transaction crosses one or more boundaries
- AW signals buffered and regenerated for each split
- W channel WLAST regenerated at split boundaries
- B channel: Collect N responses, consolidate into 1
- fub_awready suppressed until final split accepted
- Split count = N (number of splits)

### State Machine Architecture

Similar to read splitter but with additional W channel tracking:

**IDLE State:**
- Awaits new transactions on fub_aw interface
- Combinational split logic evaluates boundary crossing
- If no split: pass-through mode (single response)
- If split: buffer transaction, setup response consolidation, transition to SPLITTING

**SPLITTING State:**
- Issue current split using buffered address/length
- Track W channel beats to regenerate WLAST correctly
- Collect B channel responses (consolidate errors)
- Update next_addr and remaining_len for next split
- Return to IDLE when final split accepted

### Write Data Channel Management

**WLAST Regeneration:**

The critical challenge is regenerating WLAST at split boundaries:

**Beat Counter Tracking:**
- r_expected_beats: Beats required for current split (from split_len + 1)
- r_beat_counter: Current beat being transferred
- w_split_boundary_reached: Counter matches expected beats

**WLAST Logic:**
```
If splitting:
    WLAST = (beat_counter + 1 >= expected_beats)
Else:
    WLAST = fub_wlast (pass-through)
```

**Example (8 beats split into 1 + 7):**
- Original: 8 beats with WLAST on beat 8
- Split 1: Beat 1 → Generate WLAST (boundary reached)
- Split 2: Beats 2-8 → Original WLAST on beat 8

### Response Consolidation Logic

**CRITICAL FEATURE:** Multiple split responses must aggregate into single upstream response.

**Consolidation State:**
- r_expected_response_count: Total splits generated
- r_received_response_count: Responses received so far
- r_waiting_for_responses: Consolidation active flag
- r_consolidated_resp_status: Aggregated error status
- r_original_txn_id: Transaction ID for consolidated response

**Response Priority (Worst Error Wins):**
```
Priority: DECERR (11) > SLVERR (10) > EXOKAY (01) > OKAY (00)

if (m_axi_bresp > r_consolidated_resp_status):
    r_consolidated_resp_status = m_axi_bresp
```

**Consolidation Flow:**

1. **Setup (at transaction start):**
   - Capture original AWID
   - Initialize consolidated_resp_status = OKAY
   - Set expected_response_count = estimated splits
   - Assert waiting_for_responses flag

2. **Collection (each B response):**
   - Accept response even if fub_bready not asserted
   - OR error status into consolidated_resp_status
   - Increment received_response_count
   - Keep fub_bvalid suppressed

3. **Completion (final response):**
   - Check: received_response_count >= expected_response_count
   - Assert fub_bvalid with consolidated status
   - Wait for fub_bready handshake
   - Clear waiting_for_responses flag

**Pass-Through Mode (No Split):**
- waiting_for_responses = 0
- Direct connection: fub_b* = m_axi_b*
- Single response, no aggregation needed

### Boundary Crossing Detection

Reuses same combinational logic as read splitter (axi_split_combi):

**Inputs:**
- current_addr, current_len, ax_size, alignment_mask
- Same calculation as read splitter

**Outputs:**
- split_required, split_len, next_boundary_addr, remaining_len_after_split
- Used for both AW channel splitting and W channel beat tracking

### AW Channel Forwarding Logic

**Address/Length Calculation:**
- IDLE state: Use live fub_awaddr and calculated split_len
- SPLITTING state: Use buffered r_current_addr and split_len

**Control Signals:**
- IDLE state: Pass through from fub_aw* signals
- SPLITTING state: Use buffered r_orig_aw* signals

**Valid Signal:**
- IDLE: m_axi_awvalid = fub_awvalid
- SPLITTING: m_axi_awvalid = 1 (asserting next split)

### Ready Signal Management

**fub_awready Logic:**
- IDLE + no split: fub_awready = m_axi_awready
- IDLE + split needed: fub_awready = 0 (suppress)
- SPLITTING + intermediate: fub_awready = 0
- SPLITTING + final split: fub_awready = m_axi_awready

**W Channel Ready:**
- Always pass-through: fub_wready = m_axi_wready
- Backpressure handled naturally by AXI protocol

**B Channel Ready:**
- Consolidation mode: m_axi_bready = 1 (accept all responses)
- Pass-through mode: m_axi_bready = fub_bready
- Critical: Must accept all split responses even if upstream not ready

---

## Usage Example

### Basic Integration (4KB Boundary, Response Consolidation)

```systemverilog
axi_master_wr_splitter #(
    .AXI_ID_WIDTH       (8),
    .AXI_ADDR_WIDTH     (32),
    .AXI_DATA_WIDTH     (64),
    .AXI_USER_WIDTH     (1),
    .SPLIT_FIFO_DEPTH   (16)
) u_wr_splitter (
    .aclk               (axi_clk),
    .aresetn            (axi_rst_n),

    // 4KB boundary alignment
    .alignment_mask     (12'hFFF),

    // Error monitor backpressure
    .block_ready        (error_detected),

    // Upstream AXI write interface (from master)
    .fub_awid           (master_awid),
    .fub_awaddr         (master_awaddr),
    .fub_awlen          (master_awlen),
    .fub_awsize         (master_awsize),
    .fub_awburst        (master_awburst),
    .fub_awlock         (master_awlock),
    .fub_awcache        (master_awcache),
    .fub_awprot         (master_awprot),
    .fub_awqos          (master_awqos),
    .fub_awregion       (master_awregion),
    .fub_awuser         (master_awuser),
    .fub_awvalid        (master_awvalid),
    .fub_awready        (master_awready),

    .fub_wdata          (master_wdata),
    .fub_wstrb          (master_wstrb),
    .fub_wlast          (master_wlast),
    .fub_wuser          (master_wuser),
    .fub_wvalid         (master_wvalid),
    .fub_wready         (master_wready),

    .fub_bid            (master_bid),
    .fub_bresp          (master_bresp),
    .fub_buser          (master_buser),
    .fub_bvalid         (master_bvalid),
    .fub_bready         (master_bready),

    // Downstream AXI write interface (to memory)
    .m_axi_awid         (mem_awid),
    .m_axi_awaddr       (mem_awaddr),
    .m_axi_awlen        (mem_awlen),
    .m_axi_awsize       (mem_awsize),
    .m_axi_awburst      (mem_awburst),
    .m_axi_awlock       (mem_awlock),
    .m_axi_awcache      (mem_awcache),
    .m_axi_awprot       (mem_awprot),
    .m_axi_awqos        (mem_awqos),
    .m_axi_awregion     (mem_awregion),
    .m_axi_awuser       (mem_awuser),
    .m_axi_awvalid      (mem_awvalid),
    .m_axi_awready      (mem_awready),

    .m_axi_wdata        (mem_wdata),
    .m_axi_wstrb        (mem_wstrb),
    .m_axi_wlast        (mem_wlast),
    .m_axi_wuser        (mem_wuser),
    .m_axi_wvalid       (mem_wvalid),
    .m_axi_wready       (mem_wready),

    .m_axi_bid          (mem_bid),
    .m_axi_bresp        (mem_bresp),
    .m_axi_buser        (mem_buser),
    .m_axi_bvalid       (mem_bvalid),
    .m_axi_bready       (mem_bready),

    // Split information tracking
    .fub_split_addr     (split_addr),
    .fub_split_id       (split_id),
    .fub_split_cnt      (split_count),
    .fub_split_valid    (split_valid),
    .fub_split_ready    (split_ready)
);
```

### Response Consolidation Example

**Scenario: 2-way split with error in second split**

**Original Transaction:**
- ADDR=0x0FC0, LEN=7 (8 beats), ID=0x42

**Split Transactions:**
1. Split 1: ADDR=0x0FC0, LEN=0 (1 beat) → Response: OKAY (00)
2. Split 2: ADDR=0x1000, LEN=6 (7 beats) → Response: SLVERR (10)

**Consolidation Logic:**
```
Initial: consolidated_resp = OKAY (00)
Split 1 response: OKAY (00)
    → 00 > 00? No → Keep OKAY
Split 2 response: SLVERR (10)
    → 10 > 00? Yes → Update to SLVERR

Final consolidated response: SLVERR (10)
```

**Upstream View:**
- Master issues 1 write transaction (ADDR=0x0FC0, LEN=7, ID=0x42)
- Receives 1 response (ID=0x42, BRESP=SLVERR)
- Error correctly propagated despite partial success

---

## Design Notes

### AXI Protocol Assumptions

Same assumptions as read splitter:

**Assumption 1: Address Alignment**
- All addresses aligned to data bus width

**Assumption 2: Fixed Transfer Size**
- AWSIZE matches data width

**Assumption 3: Incrementing Bursts Only**
- Only INCR burst type supported

**Assumption 4: No Address Wraparound**
- Transactions never wrap address space

### Response Consolidation Details

**Why Consolidation is Critical:**
- AXI protocol: 1 address transaction → 1 response
- Splitting creates N address transactions → N responses
- Upstream expects exactly 1 response
- Must aggregate N responses into 1 consolidated response

**Error Priority Rationale:**
```
DECERR (Decode Error):     Transaction to invalid address
SLVERR (Slave Error):      Valid address, processing error
EXOKAY (Exclusive Okay):   Exclusive access succeeded
OKAY:                      Normal successful completion

Worst error wins → System sees most severe failure
```

**Consolidation Timing:**
- Must wait for ALL split responses before asserting fub_bvalid
- Prevents partial success reports
- Ensures atomicity from upstream perspective

### Performance Characteristics

**Latency:**
- No split: Zero added cycles (pass-through)
- Split required: 1 cycle per split + response consolidation
- Response consolidation adds latency equal to slowest split

**Throughput:**
- AW channel: Limited by split calculation (1 cycle/split)
- W channel: Full bandwidth (pass-through with WLAST regeneration)
- B channel: Responses accumulated (no upstream throughput impact)

**Area:**
- Overhead: State machine + transaction buffer + response consolidation logic
- Major components: Split FIFO + response tracking registers

### Error Handling

**Split Response Timeout:**
- Module waits indefinitely for all split responses
- No timeout mechanism (relies on downstream protocol compliance)
- Recommendation: Implement system-level timeout monitor

**FIFO Overflow:**
- Split FIFO can fill if consumer stalls
- Backpressure propagates to fub_awready
- Size FIFO >= max outstanding writes

**Data Channel Synchronization:**
- W channel must deliver exact beat count per split
- WLAST regeneration critical for correctness
- Assertions validate beat counter operation

### Integration Considerations

**Response Consolidation Requirements:**
- Downstream must return exactly 1 response per split
- Response IDs must match split transaction IDs
- All responses must eventually arrive

**WLAST Timing:**
- Generated combinationally based on beat counter
- Timing-critical path in high-speed designs
- Consider registering if timing closure issues

**Backpressure Handling:**
- B channel: Module accepts all split responses (m_axi_bready=1 during consolidation)
- Upstream backpressure (fub_bready=0) only delays final consolidated response
- Internal buffering for responses: Single register (r_consolidated_resp_status)

---

## Related Modules

### Used By
- Memory controller wrappers with boundary constraints
- Multi-bank DRAM controllers requiring aligned writes
- Bridge modules interfacing heterogeneous memory systems
- DMA engines with address range restrictions

### Uses
- **axi_split_combi.sv** - Combinational splitting logic (shared with read splitter)
- **gaxi_fifo_sync.sv** - Split information tracking FIFO
- **reset_defs.svh** - Standard reset macro definitions

### See Also
- **axi_master_rd_splitter.sv** - Read channel splitting (AR + R channels)
- **axi_split_combi.sv** - Combined read/write splitting wrapper

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_master_wr_splitter.sv`
- Tests: `val/amba/test_axi_master_wr_splitter.py`
- Testbench: `bin/CocoTBFramework/tbclasses/amba/axi_master_wr_splitter_tb.py`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- AXI Specification: AMBA AXI4 Protocol Specification (ARM IHI 0022E)
- Design Guide: `rtl/amba/PRD.md`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
