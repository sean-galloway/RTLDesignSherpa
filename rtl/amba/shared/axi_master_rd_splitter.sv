// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_rd_splitter
// Purpose: Axi Master Rd Splitter module
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

**Overview**: This module accepts AXI read transactions on the fub interface and splits them
across boundary crossings before forwarding to the master AXI interface.

**FUB_ARREADY Assertion Strategy**:
- **No Split Required**: `fub_arready` passes through `m_axi_arready` directly (immediate acceptance)
- **Split Required**: `fub_arready` is suppressed until ALL splits complete successfully

**Splitting Sequence for Boundary-Crossing Transactions**:

1. **Transaction Reception (IDLE State)**:
    - Original transaction arrives on fub_ar interface
    - Split combinational logic evaluates if boundary crossing occurs
    - If no split needed: immediate pass-through with `fub_arready = m_axi_arready`
    - If split needed: suppress `fub_arready`, transition to SPLITTING state

2. **First Split Generation (IDLE → SPLITTING)**:
    - Send first split using original address and calculated split_len
    - split_len represents beats that fit before the boundary
    - Transition to SPLITTING state, save next_addr and remaining_len

3. **Subsequent Splits (SPLITTING State)**:
    - Use saved next_addr and remaining_len for current transaction
    - Split logic recalculates if further splitting needed
    - If more splits required: send current split, update next_addr/remaining_len
    - If final split: send transaction and prepare for completion

4. **Transaction Completion**:
    - Only when the FINAL split transaction receives `m_axi_arready = 1`
    - Assert `fub_arready = 1` to complete the original fub transaction
    - Return to IDLE state for next transaction

**Key Properties**:
- FUB interface sees exactly one transaction (request → acceptance)
- Master AXI interface sees N split transactions (where N ≥ 1)
- All response data is passed through unchanged
- Total response beats equals original transaction beat count
- Split information is provided via fub_split interface for tracking

**Example Split Sequence** (4KB boundary, 64-byte beats):
```
Original: ADDR=0x0FC0, LEN=7 (8 beats, 512 bytes total)
→ Split 1: ADDR=0x0FC0, LEN=0 (1 beat, to boundary at 0x1000)
→ Split 2: ADDR=0x1000, LEN=6 (7 beats, remaining data)
```
*/

`include "reset_defs.svh"
module axi_master_rd_splitter
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
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Block ready from the errmon
    input  logic                       block_ready,

    // Slave AXI Interface
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_arid,
    input  logic [AW-1:0]              fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [UW-1:0]              fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_rid,
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [UW-1:0]              fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

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
    logic [IW-1:0]  r_orig_arid;
    logic [AW-1:0]  r_orig_araddr;
    logic [7:0]     r_orig_arlen;
    logic [2:0]     r_orig_arsize;
    logic [1:0]     r_orig_arburst;
    logic           r_orig_arlock;
    logic [3:0]     r_orig_arcache;
    logic [2:0]     r_orig_arprot;
    logic [3:0]     r_orig_arqos;
    logic [3:0]     r_orig_arregion;
    logic [UW-1:0]  r_orig_aruser;

    // Current split transaction state
    logic [AW-1:0]  r_current_addr;
    logic [7:0]     r_current_len;
    logic [7:0]     r_split_count;

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
            w_current_addr = fub_araddr;
            w_current_len = fub_arlen;
            w_current_size = fub_arsize;
        end else begin
            // SPLITTING: Use buffered split state
            w_current_addr = r_current_addr;
            w_current_len = r_current_len;
            w_current_size = r_orig_arsize;
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
        .AW                        (AW),
        .DW                        (DW)
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
        .transaction_valid         (fub_arvalid),

        // Essential outputs
        .split_required            (w_split_required),
        .split_len                 (w_split_len),
        .next_boundary_addr        (w_next_boundary_addr),
        .remaining_len_after_split (w_remaining_len_after_split),
        .new_split_needed          (w_new_split_needed)
    );

    //===========================================================================
    // State Management
    //===========================================================================

    // Determine if we're sending the final split transaction
    logic w_is_final_split;
    assign w_is_final_split = (r_split_state == SPLITTING) && !w_split_required;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_split_state <= IDLE;
            r_current_addr <= '0;
            r_current_len <= '0;
            r_split_count <= 8'd0;

            // Reset buffered transaction
            r_orig_arid <= '0;
            r_orig_araddr <= '0;
            r_orig_arlen <= '0;
            r_orig_arsize <= '0;
            r_orig_arburst <= '0;
            r_orig_arlock <= '0;
            r_orig_arcache <= '0;
            r_orig_arprot <= '0;
            r_orig_arqos <= '0;
            r_orig_arregion <= '0;
            r_orig_aruser <= '0;
        end else begin
            case (r_split_state)
                IDLE: begin
                    if (fub_arvalid && m_axi_arready && !block_ready) begin
                        // Buffer the original transaction
                        r_orig_arid <= fub_arid;
                        r_orig_araddr <= fub_araddr;
                        r_orig_arlen <= fub_arlen;
                        r_orig_arsize <= fub_arsize;
                        r_orig_arburst <= fub_arburst;
                        r_orig_arlock <= fub_arlock;
                        r_orig_arcache <= fub_arcache;
                        r_orig_arprot <= fub_arprot;
                        r_orig_arqos <= fub_arqos;
                        r_orig_arregion <= fub_arregion;
                        r_orig_aruser <= fub_aruser;

                        if (w_new_split_needed) begin
                            // Splitting required - transition to SPLITTING state
                            r_split_state <= SPLITTING;
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= 8'd2; // First split sent, second split next
                        end
                        // If no split needed, stay in IDLE (pass-through transaction)
                    end
                end

                SPLITTING: begin
                    if (m_axi_arvalid && m_axi_arready) begin
                        if (w_split_required) begin
                            // More splits needed - continue splitting
                            r_current_addr <= w_next_boundary_addr;
                            r_current_len <= w_remaining_len_after_split;
                            r_split_count <= r_split_count + 8'd1;
                            // Stay in SPLITTING state
                        end else begin
                            // Final split transaction completed - return to IDLE
                            r_split_state <= IDLE;
                            r_split_count <= 8'd0;
                        end
                    end
                end

                default: r_split_state <= IDLE;
            endcase
        end
    )


    //===========================================================================
    // AXI Signal Assignments
    //===========================================================================

    // AR Channel - Master side
    always_comb begin
        // Address and length based on split logic
        m_axi_araddr = w_current_addr;
        m_axi_arlen = w_split_required ? w_split_len : w_current_len;

        // Use buffered signals when in SPLITTING state, original signals when IDLE
        if (r_split_state == IDLE) begin
            m_axi_arid = fub_arid;
            m_axi_arsize = fub_arsize;
            m_axi_arburst = fub_arburst;
            m_axi_arlock = fub_arlock;
            m_axi_arcache = fub_arcache;
            m_axi_arprot = fub_arprot;
            m_axi_arqos = fub_arqos;
            m_axi_arregion = fub_arregion;
            m_axi_aruser = fub_aruser;
        end else begin
            m_axi_arid = r_orig_arid;
            m_axi_arsize = r_orig_arsize;
            m_axi_arburst = r_orig_arburst;
            m_axi_arlock = r_orig_arlock;
            m_axi_arcache = r_orig_arcache;
            m_axi_arprot = r_orig_arprot;
            m_axi_arqos = r_orig_arqos;
            m_axi_arregion = r_orig_arregion;
            m_axi_aruser = r_orig_aruser;
        end

        // Valid signal
        case (r_split_state)
            IDLE: m_axi_arvalid = fub_arvalid;
            SPLITTING: m_axi_arvalid = 1'b1;
            default: m_axi_arvalid = 1'b0;
        endcase
    end

    // AR Channel - Slave side ready logic
    always_comb begin
        case (r_split_state)
            IDLE: begin
                if (w_new_split_needed) begin
                    // Split required - suppress fub_arready until all splits complete
                    fub_arready = 1'b0;
                end else begin
                    // No split needed - pass through ready immediately
                    fub_arready = m_axi_arready && !block_ready;
                end
            end
            SPLITTING: begin
                // Only assert ready when final split transaction is accepted
                fub_arready = w_is_final_split && m_axi_arready && !block_ready;
            end
            default: begin
                fub_arready = 1'b0;
            end
        endcase
    end

    // R Channel - Pass through all signals
    assign fub_rid = m_axi_rid;
    assign fub_rdata = m_axi_rdata;
    assign fub_rresp = m_axi_rresp;
    assign fub_ruser = m_axi_ruser;
    assign fub_rvalid = m_axi_rvalid;
    assign fub_rlast = m_axi_rlast;
    assign m_axi_rready = fub_rready;

    //===========================================================================
    // Split information FIFO
    //===========================================================================

    // Pack the split info for the FIFO
    logic [AW+IW+8-1:0] split_fifo_din;
    logic w_split_fifo_valid;

    // Write split info when original transaction is accepted (fub_arready asserts)
    assign w_split_fifo_valid = fub_arvalid && fub_arready;

    // Always use the original transaction data at the time of acceptance
    always_comb begin
        if (r_split_state == IDLE) begin
            // IDLE state: use live inputs (original transaction)
            split_fifo_din = {fub_araddr,
                                fub_arid,
                                w_new_split_needed ? 8'd2 : 8'd1};  // Estimate split count
        end else begin
            // SPLITTING state: use buffered original transaction data
            split_fifo_din = {r_orig_araddr,
                                r_orig_arid,
                                r_split_count};  // Actual split count
        end
    end

    // Instantiate the FIFO for split information
    gaxi_fifo_sync #(
        .REGISTERED        (0), // muxed output mode
        .DATA_WIDTH        (AW + IW + 8),
        .DEPTH             (SPLIT_FIFO_DEPTH),
        .INSTANCE_NAME     ("SPLIT_FIFO")
    ) inst_split_info_fifo(
        .axi_aclk        (aclk),
        .axi_aresetn     (aresetn),
        .wr_valid        (w_split_fifo_valid),
        .wr_data         (split_fifo_din),
        .rd_ready        (fub_split_ready),
        .rd_valid        (fub_split_valid),
        .rd_data         ({fub_split_addr, fub_split_id, fub_split_cnt}),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready        (),  // Not used
        .count          ()    // Not used
        /* verilator lint_on PINCONNECTEMPTY */
    );

    //===========================================================================
    // Additional Assertions for Integration Validation
    //===========================================================================

    // synopsys translate_off
    // Ensure state machine consistency
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
            if (r_split_state == IDLE && fub_arvalid && w_new_split_needed) begin
                assert (fub_arready == 1'b0) else
                    $error("fub_arready should be suppressed when split needed in IDLE");
            end

            if (r_split_state == SPLITTING && !w_is_final_split) begin
                assert (fub_arready == 1'b0) else
                    $error("fub_arready should be suppressed during intermediate splits");
            end

            // Verify transaction buffering
            if (r_split_state == SPLITTING) begin
                assert (r_orig_arid != '0 || r_orig_araddr != '0) else
                    $error("Original transaction should be buffered in SPLITTING state");
            end

            // Verify split info FIFO write timing
            if (w_split_fifo_valid) begin
                assert (fub_arvalid && fub_arready) else
                    $error("Split info should only be written when transaction is accepted");
            end
        end
        /* verilator lint_on SYNCASYNCNET */
    end
    // synopsys translate_on

endmodule : axi_master_rd_splitter
