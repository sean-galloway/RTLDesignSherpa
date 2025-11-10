// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_wr_splitter
// Purpose: Axi Master Wr Splitter module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
/*
### Assumption 1: Address is always aligned to the data bus width
**Assumption**: All AXI transactions are aligned to the data bus width.

- **Implication**: `AxADDRESS` is always set to match the data bus width
    - if DATA_WIDTH = 512bits, `AxADDRESS` is always 64-byte aligned

### Assumption 2: Fixed Transfer Size
**Assumption**: All AXI transfers use the maximum transfer size equal to the bus width.

- **Implication**: `AxSIZE` is always set to match the data bus width
- **Rationale**: Maximizes bus utilization and simplifies address alignment
- **Implementation**:
    - 32-bit bus → `AxSIZE = 3'b010` (4 bytes)
    - 64-bit bus → `AxSIZE = 3'b011` (8 bytes)
    - 128-bit bus → `AxSIZE = 3'b100` (16 bytes)

### Assumption 3: Incrementing Bursts Only
**Assumption**: All AXI bursts use incrementing address mode (`AxBURST = 2'b01`).

- **Implication**: No FIXED (`2'b00`) or WRAP (`2'b10`) bursts supported
- **Rationale**: Simplifies address generation logic and covers most use cases
- **Benefit**: Eliminates wrap boundary calculations and fixed address handling

### Assumption 4: No Address Wraparound
**Assumption**: Transactions never wrap around the top of address space (0xFFFFFFFF -> 0x00000000).

- **Implication**: No wraparound handling in boundary crossing logic
- **Rationale**: Real systems never allow this condition due to memory layout and software design
- **Benefit**: Dramatically simplified boundary crossing detection logic

### Transaction Splitting Flow Documentation

**Overview**: This module accepts AXI write transactions on the fub interface and splits them
across boundary crossings before forwarding to the master AXI interface.

**FUB_AWREADY Assertion Strategy**:
- **No Split Required**: `fub_awready` passes through `m_axi_awready` directly (immediate acceptance)
- **Split Required**: `fub_awready` is suppressed until ALL splits complete successfully

**Splitting Sequence for Boundary-Crossing Transactions**:

1. **Transaction Reception (IDLE State)**:
    - Original transaction arrives on fub_aw interface
    - Split combinational logic evaluates if boundary crossing occurs
    - If no split needed: immediate pass-through with `fub_awready = m_axi_awready`
    - If split needed: suppress `fub_awready`, transition to SPLITTING state

2. **First Split Generation (IDLE → SPLITTING)**:
    - Send first split using original address and calculated split_len
    - split_len represents beats that fit before the boundary
    - Transition to SPLITTING state, save next_addr and remaining_len

3. **Subsequent Splits (SPLITTING State)**:
    - Use saved next_addr and remaining_len for current transaction
    - Split logic recalculates if further splitting needed
    - If more splits required: send current split, update next_addr/remaining_len
    - If final split: send transaction and prepare for completion

4. **Write Data Flow**:
    - Write data flows through unchanged (pass-through)
    - WLAST is regenerated for each split transaction
    - Data beats are distributed across split transactions in order

5. **Response Consolidation (CRITICAL FOR WRITE TRANSACTIONS)**:
    - **Multiple Split Responses**: Each split transaction generates one response
    - **Response OR'ing/Aggregation**: Multiple responses are consolidated into one
    - **Error Priority**: Worst error response is preserved (DECERR > SLVERR > EXOKAY > OKAY)
    - **Single Response**: Original transaction receives exactly ONE response regardless of splits
    - **Transaction Completion**: Only when final consolidated response is sent

**Key Properties**:
- FUB interface sees exactly one write transaction (request → acceptance → single response)
- Master AXI interface sees N split transactions (where N ≥ 1) with N responses
- Write data is passed through with regenerated WLAST for each split
- **RESPONSE CONSOLIDATION**: N split responses are OR'd/aggregated into 1 upstream response
- Split information is provided via fub_split interface for tracking

**Response Consolidation Details**:
- **Input**: N responses from split transactions (worst case N responses)
- **Logic**: OR together error conditions, preserve worst error status
- **Output**: Single consolidated response with worst error status
- **Timing**: Response sent only after ALL split responses received

**Example Split Sequence with Response Consolidation** (4KB boundary, 64-byte beats):
```
Original: ADDR=0x0FC0, LEN=7 (8 beats, 512 bytes total)
→ Split 1: ADDR=0x0FC0, LEN=0 (1 beat, to boundary at 0x1000) → Response 1: OKAY
→ Split 2: ADDR=0x1000, LEN=6 (7 beats, remaining data)      → Response 2: OKAY
→ Consolidation: Response 1 OR Response 2 = OKAY             → Final Response: OKAY
→ FUB sees: 1 transaction, 8 data beats, 1 response ✓
```
*/

`include "reset_defs.svh"

module axi_master_wr_splitter
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    // FIFO depth
    parameter int SPLIT_FIFO_DEPTH  = 4,
    // short names
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Alignment mask signal (12-bit)
    input  logic [11:0] alignment_mask,

    // Master AXI Interface
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Block ready from the errmon
    input  logic                       block_ready,

    // Slave AXI Interface
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [UW-1:0]              fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [UW-1:0]              fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [UW-1:0]              fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Output split information
    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready
);

    //===========================================================================
    // Parameter Validation
    //===========================================================================
    initial begin
        assert (DW inside {32, 64, 128, 256, 512, 1024}) else
            $fatal(1, "AXI_DATA_WIDTH must be power of 2 between 32 and 1024 bits");
    end

    //===========================================================================
    // State definitions
    //===========================================================================
    typedef enum logic [1:0] {
        IDLE      = 2'b01,
        SPLITTING = 2'b10
    } split_state_t;

    split_state_t r_split_state;

    //===========================================================================
    // Transaction Storage - Buffer original transaction
    //===========================================================================

    // Buffered original transaction (captured when first accepted)
    logic [IW-1:0]  r_orig_awid;
    logic [AW-1:0]  r_orig_awaddr;
    logic [7:0]     r_orig_awlen;
    logic [2:0]     r_orig_awsize;
    logic [1:0]     r_orig_awburst;
    logic           r_orig_awlock;
    logic [3:0]     r_orig_awcache;
    logic [2:0]     r_orig_awprot;
    logic [3:0]     r_orig_awqos;
    logic [3:0]     r_orig_awregion;
    logic [UW-1:0]  r_orig_awuser;

    // Current split transaction state
    logic [AW-1:0]  r_current_addr;
    logic [7:0]     r_current_len;
    logic [7:0]     r_split_count;

    // Data channel tracking for WLAST generation
    logic [7:0]     r_expected_beats;      // Expected beats for current split
    logic [7:0]     r_beat_counter;        // Current beat counter
    logic           r_data_splitting;      // Flag indicating we're handling split data

    //===========================================================================
    // Response Consolidation Logic
    //===========================================================================

    // Response consolidation state - OR's multiple split responses into one
    logic [7:0]     r_expected_response_count;   // How many responses we expect total
    logic [7:0]     r_received_response_count;   // How many split responses we've received
    logic           r_waiting_for_responses;     // Currently collecting split responses
    logic [IW-1:0]  r_original_txn_id;          // Original transaction ID for response
    logic [1:0]     r_consolidated_resp_status; // Consolidated response status (OR'd errors)
    logic [UW-1:0]  r_consolidated_buser;       // User field for consolidated response

    //===========================================================================
    // Current Transaction Selection Logic
    //===========================================================================

    // Select current address and length based on splitting state
    logic [AW-1:0]  w_current_addr;
    logic [7:0]     w_current_len;
    logic [2:0]     w_current_size;

    always_comb begin
        if (r_split_state == IDLE) begin
            // IDLE: Use original transaction inputs
            w_current_addr = fub_awaddr;
            w_current_len = fub_awlen;
            w_current_size = fub_awsize;
        end else begin
            // SPLITTING: Use buffered split state
            w_current_addr = r_current_addr;
            w_current_len = r_current_len;
            w_current_size = r_orig_awsize;
        end
    end

    //===========================================================================
    // Instantiate AXI Split Combinational Logic Module
    //===========================================================================

    // Signals from the split combinational logic
    logic           w_split_required;
    logic [7:0]     w_split_len;
    logic [AW-1:0]  w_next_boundary_addr;
    logic [7:0]     w_remaining_len_after_split;
    logic           w_new_split_needed;

    axi_split_combi #(
        .AW(AW),
        .DW(DW)
    ) inst_axi_split_combi (
        // Clock and reset for assertions
        .aclk                      (aclk),
        .aresetn                   (aresetn),

        // Inputs
        .current_addr              (w_current_addr),
        .current_len               (w_current_len),
        .ax_size                   (w_current_size),
        .alignment_mask            (alignment_mask),
        .is_idle_state             (r_split_state == IDLE),
        .transaction_valid         (fub_awvalid),

        // Essential outputs
        .split_required            (w_split_required),
        .split_len                 (w_split_len),
        .next_boundary_addr        (w_next_boundary_addr),
        .remaining_len_after_split (w_remaining_len_after_split),
        .new_split_needed          (w_new_split_needed)
    );

    //===========================================================================
    // State Management with Response Consolidation Setup
    //===========================================================================

    // Determine if we're sending the final split transaction
    logic w_is_final_split;
    assign w_is_final_split = (r_split_state == SPLITTING) && !w_split_required;

    // WLAST generation signals
    logic w_split_boundary_reached;
    logic w_generate_wlast;

    assign w_split_boundary_reached = (r_beat_counter + 1 >= r_expected_beats);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_split_state <= IDLE;
            r_current_addr <= '0;
            r_current_len <= '0;
            r_split_count <= 8'd0;

            // Reset buffered transaction
            r_orig_awid <= '0;
            r_orig_awaddr <= '0;
            r_orig_awlen <= '0;
            r_orig_awsize <= '0;
            r_orig_awburst <= '0;
            r_orig_awlock <= '0;
            r_orig_awcache <= '0;
            r_orig_awprot <= '0;
            r_orig_awqos <= '0;
            r_orig_awregion <= '0;
            r_orig_awuser <= '0;

            // Reset data channel tracking
            r_expected_beats <= '0;
            r_beat_counter <= '0;
            r_data_splitting <= 1'b0;

            // Reset response consolidation state
            r_expected_response_count <= '0;
            r_received_response_count <= '0;
            r_waiting_for_responses <= 1'b0;
            r_original_txn_id <= '0;
            r_consolidated_resp_status <= 2'b00; // OKAY
            r_consolidated_buser <= '0;

        end else begin
            case (r_split_state)
                IDLE: begin
                    if (fub_awvalid && m_axi_awready && !block_ready) begin
                        // Buffer the original transaction
                        r_orig_awid <= fub_awid;
                        r_orig_awaddr <= fub_awaddr;
                        r_orig_awlen <= fub_awlen;
                        r_orig_awsize <= fub_awsize;
                        r_orig_awburst <= fub_awburst;
                        r_orig_awlock <= fub_awlock;
                        r_orig_awcache <= fub_awcache;
                        r_orig_awprot <= fub_awprot;
                        r_orig_awqos <= fub_awqos;
                        r_orig_awregion <= fub_awregion;
                        r_orig_awuser <= fub_awuser;

                        // Setup response consolidation for this transaction
                        r_original_txn_id <= fub_awid;
                        r_consolidated_resp_status <= 2'b00; // Start with OKAY
                        r_consolidated_buser <= fub_awuser;

                        if (w_new_split_needed) begin
                            // Splitting required - transition to SPLITTING state
                            r_split_state <= SPLITTING;
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= 8'd2; // First split sent, second split next

                            // Setup data tracking for first split
                            r_expected_beats <= w_split_len + 1; // Convert AXI encoding to beat count
                            r_beat_counter <= '0;
                            r_data_splitting <= 1'b1;

                            // RESPONSE CONSOLIDATION: Setup for multiple responses
                            r_expected_response_count <= 8'd2; // Start with 2, will update as more splits found
                            r_received_response_count <= '0;
                            r_waiting_for_responses <= 1'b1; // Enable response consolidation
                        end else begin
                            // No split needed - setup for passthrough
                            r_expected_beats <= fub_awlen + 1;
                            r_beat_counter <= '0;
                            r_data_splitting <= 1'b0;

                            // RESPONSE CONSOLIDATION: Single response expected (pass-through mode)
                            r_expected_response_count <= 8'd1;
                            r_received_response_count <= '0;
                            r_waiting_for_responses <= 1'b0; // No consolidation needed
                        end
                    end
                end

                SPLITTING: begin
                    if (m_axi_awvalid && m_axi_awready) begin
                        if (w_split_required) begin
                            // More splits needed - continue splitting
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= r_split_count + 8'd1;

                            // RESPONSE CONSOLIDATION: Increment expected response count
                            r_expected_response_count <= r_expected_response_count + 8'd1;

                            // Note: beat tracking updated in data section below
                        end else begin
                            // Final split transaction completed - return to IDLE
                            r_split_state <= IDLE;
                            r_split_count <= 8'd0;

                            // Note: beat tracking updated in data section below
                        end
                    end
                end

                default: r_split_state <= IDLE;
            endcase

            // Data beat counter management
            if (m_axi_wvalid && m_axi_wready) begin
                r_beat_counter <= r_beat_counter + 1;

                // Check if we've completed the current split
                if (w_split_boundary_reached) begin
                    // Current split done - reset counter and setup for next split
                    r_beat_counter <= '0;

                    // Update expected beats for next split
                    if (r_split_state == SPLITTING) begin
                        if (w_split_required) begin
                            // More splits coming - use next split length
                            r_expected_beats <= w_split_len + 1;
                        end else begin
                            // This is/was the final split - use final length
                            r_expected_beats <= w_current_len + 1;
                        end
                    end else begin
                        // No more splits - transaction complete
                        r_data_splitting <= 1'b0;
                    end
                end
            end

            // RESPONSE CONSOLIDATION: Process incoming split responses
            if (m_axi_bvalid && m_axi_bready) begin
                // Received a split response - consolidate it
                r_received_response_count <= r_received_response_count + 8'd1;

                // OR together error conditions - keep worst response status
                // Priority: DECERR (3) > SLVERR (2) > EXOKAY (1) > OKAY (0)
                if (m_axi_bresp > r_consolidated_resp_status) begin
                    r_consolidated_resp_status <= m_axi_bresp;
                end

                // Check if this was the final response to consolidate
                if (r_received_response_count + 8'd1 >= r_expected_response_count) begin
                    // All responses received - ready to send consolidated response
                    r_waiting_for_responses <= 1'b0;
                    // Reset counters for next transaction
                    r_received_response_count <= '0;
                    r_expected_response_count <= '0;
                end
            end
        end
    )


    //===========================================================================
    // AXI Signal Assignments - Address Channel
    //===========================================================================

    // AW Channel - Master side
    always_comb begin
        // Address and length based on split logic
        m_axi_awaddr = w_current_addr;
        m_axi_awlen = w_split_required ? w_split_len : w_current_len;

        // Use buffered signals when in SPLITTING state, original signals when IDLE
        if (r_split_state == IDLE) begin
            m_axi_awid = fub_awid;
            m_axi_awsize = fub_awsize;
            m_axi_awburst = fub_awburst;
            m_axi_awlock = fub_awlock;
            m_axi_awcache = fub_awcache;
            m_axi_awprot = fub_awprot;
            m_axi_awqos = fub_awqos;
            m_axi_awregion = fub_awregion;
            m_axi_awuser = fub_awuser;
        end else begin
            m_axi_awid = r_orig_awid;
            m_axi_awsize = r_orig_awsize;
            m_axi_awburst = r_orig_awburst;
            m_axi_awlock = r_orig_awlock;
            m_axi_awcache = r_orig_awcache;
            m_axi_awprot = r_orig_awprot;
            m_axi_awqos = r_orig_awqos;
            m_axi_awregion = r_orig_awregion;
            m_axi_awuser = r_orig_awuser;
        end

        // Valid signal
        case (r_split_state)
            IDLE: m_axi_awvalid = fub_awvalid;
            SPLITTING: m_axi_awvalid = 1'b1;
            default: m_axi_awvalid = 1'b0;
        endcase
    end

    // AW Channel - Slave side ready logic
    always_comb begin
        case (r_split_state)
            IDLE: begin
                if (w_new_split_needed) begin
                    // Split required - suppress fub_awready until all splits complete
                    fub_awready = 1'b0;
                end else begin
                    // No split needed - pass through ready immediately
                    fub_awready = m_axi_awready && !block_ready;
                end
            end
            SPLITTING: begin
                // Only assert ready when final split transaction is accepted
                fub_awready = w_is_final_split && m_axi_awready && !block_ready;
            end
            default: begin
                fub_awready = 1'b0;
            end
        endcase
    end

    //===========================================================================
    // Data Channel Management with WLAST Generation
    //===========================================================================

    // WLAST generation logic
    always_comb begin
        if (r_data_splitting) begin
            // For split transactions: generate WLAST at split boundaries
            w_generate_wlast = fub_wvalid && w_split_boundary_reached;
        end else begin
            // For non-split transactions: use original WLAST
            w_generate_wlast = fub_wlast;
        end
    end

    // W Channel - Pass through with modified WLAST
    assign m_axi_wdata = fub_wdata;
    assign m_axi_wstrb = fub_wstrb;
    assign m_axi_wuser = fub_wuser;
    assign m_axi_wlast = w_generate_wlast;
    assign m_axi_wvalid = fub_wvalid;
    assign fub_wready = m_axi_wready;

    //===========================================================================
    // Write Response Channel with Consolidation
    //===========================================================================

    // Response consolidation logic - OR's multiple split responses into one
    logic w_should_send_consolidated_response;
    logic w_is_final_response;

    // Determine when we have the final response to consolidate
    assign w_is_final_response = (r_received_response_count + 8'd1 >= r_expected_response_count);
    assign w_should_send_consolidated_response = !r_waiting_for_responses || w_is_final_response;

    // B Channel - Response consolidation logic
    always_comb begin
        if (r_waiting_for_responses) begin
            // CONSOLIDATION MODE: Collecting multiple split responses into one
            fub_bid = r_original_txn_id;  // Use original transaction ID
            fub_bresp = w_is_final_response ? r_consolidated_resp_status : 2'b00; // Use consolidated status for final response
            fub_buser = r_consolidated_buser; // Use stored user field
            fub_bvalid = m_axi_bvalid && w_is_final_response; // Only assert valid for final consolidated response
            m_axi_bready = fub_bready || !w_is_final_response; // Accept all responses during consolidation
        end else begin
            // PASS-THROUGH MODE: Single response, no consolidation needed
            fub_bid = m_axi_bid;
            fub_bresp = m_axi_bresp;
            fub_buser = m_axi_buser;
            fub_bvalid = m_axi_bvalid;
            m_axi_bready = fub_bready;
        end
    end

    //===========================================================================
    // Split information FIFO
    //===========================================================================

    // Pack the split info for the FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    logic w_split_fifo_valid;

    // Write split info when original transaction is accepted
    assign w_split_fifo_valid = fub_awvalid && fub_awready;

    // Always use the original transaction data at the time of acceptance
    always_comb begin
        if (r_split_state == IDLE) begin
            // IDLE state: use live inputs (original transaction)
            split_fifo_din = {fub_awaddr,
                                fub_awid,
                                w_new_split_needed ? 8'd2 : 8'd1};  // Estimate split count
        end else begin
            // SPLITTING state: use buffered original transaction data
            split_fifo_din = {r_orig_awaddr,
                                r_orig_awid,
                                r_split_count};  // Actual split count
        end
    end

    // Instantiate the FIFO for split information
    gaxi_fifo_sync #(
        .REGISTERED(0), // muxed output mode
        .DATA_WIDTH(AW + IW + 8),
        .DEPTH(SPLIT_FIFO_DEPTH),
        .INSTANCE_NAME("SPLIT_FIFO")
    ) inst_split_info_fifo (
        .axi_aclk(aclk),
        .axi_aresetn(aresetn),
        .wr_valid(w_split_fifo_valid),
        .wr_data(split_fifo_din),
        .rd_ready(fub_split_ready),
        .rd_valid(fub_split_valid),
        .rd_data({fub_split_addr, fub_split_id, fub_split_cnt}),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready(),  // Not used
        .count()    // Not used
        /* verilator lint_on PINCONNECTEMPTY */
    );

    //===========================================================================
    // Assertions for Validation
    //===========================================================================

    // synopsys translate_off
    always_ff @(posedge aclk) begin
        /* verilator lint_off SYNCASYNCNET */
        if (aresetn) begin
            // Verify split count is reasonable
            /* verilator lint_off CMPCONST */
            /* verilator lint_off UNSIGNED */
            assert (r_split_count >= 0 && r_split_count <= 255) else
                $error("r_split_count (%0d) out of reasonable range", r_split_count);
            /* verilator lint_on CMPCONST */
            /* verilator lint_on UNSIGNED */

            // Verify ready logic correctness
            if (r_split_state == IDLE && fub_awvalid && w_new_split_needed) begin
                assert (fub_awready == 1'b0) else
                    $error("fub_awready should be suppressed when split needed in IDLE");
            end

            if (r_split_state == SPLITTING && !w_is_final_split) begin
                assert (fub_awready == 1'b0) else
                    $error("fub_awready should be suppressed during intermediate splits");
            end

            // Verify transaction buffering
            if (r_split_state == SPLITTING) begin
                assert (r_orig_awid != '0 || r_orig_awaddr != '0) else
                    $error("Original transaction should be buffered in SPLITTING state");
            end

            // Verify response consolidation logic
            if (r_waiting_for_responses) begin
                assert (r_received_response_count <= r_expected_response_count) else
                    $error("Received more responses (%0d) than expected (%0d)",
                            r_received_response_count, r_expected_response_count);

                // Verify fub_bvalid is suppressed until final response
                if (m_axi_bvalid && !w_is_final_response) begin
                    assert (fub_bvalid == 1'b0) else
                        $error("fub_bvalid should be suppressed during response consolidation");
                end

                // Verify m_axi_bready accepts responses during consolidation
                if (m_axi_bvalid && !w_is_final_response) begin
                    assert (m_axi_bready == 1'b1) else
                        $error("m_axi_bready should accept responses during consolidation");
                end
            end

            // Verify split info FIFO write timing
            if (w_split_fifo_valid) begin
                assert (fub_awvalid && fub_awready) else
                    $error("Split info should only be written when transaction is accepted");
            end

            // Verify data channel beat tracking
            if (r_data_splitting && m_axi_wvalid) begin
                assert (r_beat_counter < r_expected_beats) else
                    $error("Beat counter (%0d) exceeded expected beats (%0d)",
                            r_beat_counter, r_expected_beats);
            end

            // Verify WLAST timing for split transactions
            if (r_data_splitting && m_axi_wvalid && m_axi_wready && m_axi_wlast) begin
                assert (w_split_boundary_reached) else
                    $error("WLAST generated but not at split boundary");
            end
        end
        /* verilator lint_on SYNCASYNCNET */
    end
    // synopsys translate_on

endmodule : axi_master_wr_splitter
