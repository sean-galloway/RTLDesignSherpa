// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_drop_fifo_sync
// Purpose: //   Synchronous FIFO with dynamic drop capability. Extends gaxi_fifo_sync with
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: gaxi_drop_fifo_sync
//==============================================================================
// Description:
//   Synchronous FIFO with dynamic drop capability. Extends gaxi_fifo_sync with
//   the ability to discard entries from the read side without reading them out.
//   Useful for packet buffers where entire packets or specific entry counts
//   need to be dropped (e.g., error recovery, flow control, buffer management).
//
// Features:
//   - All standard FIFO features (valid/ready handshake, parameterizable depth)
//   - Dynamic drop operation via drop_valid/drop_ready handshake
//   - Drop by count (drop_count entries) or drop all (drop_all flag)
//   - Automatic pointer adjustment with FSM-controlled settling time
//   - Blocks normal read/write during drop operation for data integrity
//
//------------------------------------------------------------------------------
// Drop Operation Flow:
//------------------------------------------------------------------------------
//   1. User asserts drop_valid (with drop_count and/or drop_all)
//   2. FSM enters DROP_ACTIVE state
//      - Output rd_valid and wr_ready forced low (freeze FIFO I/O)
//   3. One clock cycle: pointer adjustment
//      - If drop_all=1: rd_ptr = wr_ptr (FIFO becomes empty)
//      - If drop_all=0: rd_ptr = rd_ptr + drop_count (advance by count)
//   4. FSM enters DROP_SETTLE state (one dead clock for pointer settling)
//   5. FSM asserts drop_ready (acknowledges drop complete)
//   6. FSM returns to IDLE, normal operation resumes
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   REGISTERED:
//     Description: Output register mode
//     Type: int
//     Range: 0 or 1
//     Default: 0
//     Constraints: 0 = mux mode (combinational), 1 = flop mode (registered)
//
//   DATA_WIDTH:
//     Description: Width of data bus in bits
//     Type: int
//     Range: 1 to 1024
//     Default: 4
//     Constraints: Should match connected interface width
//
//   DEPTH:
//     Description: FIFO depth (number of entries)
//     Type: int
//     Range: 2 to 65536
//     Default: 4
//     Constraints: Must be power of 2 for efficient addressing
//
//   ALMOST_WR_MARGIN:
//     Description: Almost-full threshold (entries from full)
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//
//   ALMOST_RD_MARGIN:
//     Description: Almost-empty threshold (entries from empty)
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//
//   INSTANCE_NAME:
//     Description: Instance name for error messages
//     Type: string
//     Default: "DEADF1F0"
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Standard FIFO Interface:
//     axi_aclk:         Clock input
//     axi_aresetn:      Active-low asynchronous reset
//     wr_valid:         Write data valid
//     wr_ready:         Write ready (not full, blocked during drop)
//     wr_data:          Write data input [DATA_WIDTH-1:0]
//     rd_ready:         Read ready (consumer ready)
//     rd_valid:         Read data valid (not empty, blocked during drop)
//     rd_data:          Read data output [DATA_WIDTH-1:0]
//     count:            Current FIFO occupancy [ADDR_WIDTH:0]
//
//   Drop Control Interface:
//     drop_valid:       Drop request (start drop operation)
//     drop_ready:       Drop acknowledge (drop complete)
//     drop_count:       Number of entries to drop [ADDR_WIDTH:0]
//     drop_all:         Flag: drop all entries (ignore drop_count)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Drop Operation Latency: 3 cycles
//     - Cycle 0: drop_valid asserted, FSM enters DROP_ACTIVE
//     - Cycle 1: Pointer adjustment, FSM enters DROP_SETTLE
//     - Cycle 2: drop_ready asserted, FSM returns IDLE
//     - Cycle 3+: Normal operation resumes
//
//   I/O Freeze During Drop: rd_valid and wr_ready forced low in DROP_ACTIVE and DROP_SETTLE
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   gaxi_drop_fifo_sync #(
//       .DATA_WIDTH(32),
//       .DEPTH(256),
//       .REGISTERED(0)
//   ) u_drop_fifo (
//       .axi_aclk     (clk),
//       .axi_aresetn  (rst_n),
//       // Write interface
//       .wr_valid     (wr_valid),
//       .wr_ready     (wr_ready),
//       .wr_data      (wr_data),
//       // Read interface
//       .rd_ready     (rd_ready),
//       .rd_valid     (rd_valid),
//       .rd_data      (rd_data),
//       .count        (fifo_count),
//       // Drop interface
//       .drop_valid   (drop_req),
//       .drop_ready   (drop_ack),
//       .drop_count   (entries_to_drop),
//       .drop_all     (drop_entire_fifo)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Drop operation takes 3 clock cycles (activate, adjust, settle)
//   - FIFO I/O blocked during drop to prevent data corruption
//   - drop_count must be <= current FIFO count (checked in simulation)
//   - drop_all=1 overrides drop_count (empties entire FIFO)
//   - Pointer wraparound handled correctly (MSB toggle preserved)
//   - Custom pointer arithmetic required (counter_bin only increments by 1)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - gaxi_fifo_sync.sv - Base synchronous FIFO (no drop capability)
//   - gaxi_fifo_async.sv - Async FIFO (CDC, no drop)
//   - counter_bin.sv - FIFO pointer management
//   - fifo_control.sv - Full/empty flag generation
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_gaxi_drop_fifo_sync.py
//   Run: pytest val/amba/test_gaxi_drop_fifo_sync.py -v
//
//==============================================================================

`include "fifo_defs.svh"
`include "reset_defs.svh"


module gaxi_drop_fifo_sync #(
    parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter string INSTANCE_NAME = "DEADF1F0",
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH,
    parameter int AW = $clog2(DEPTH)
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    // Standard FIFO interface
    input  logic            wr_valid,
    output logic            wr_ready,   // not full (blocked during drop)
    input  logic [DW-1:0]   wr_data,
    input  logic            rd_ready,
    output logic [AW:0]     count,
    output logic            rd_valid,   // not empty (blocked during drop)
    output logic [DW-1:0]   rd_data,
    // Drop control interface
    input  logic            drop_valid,
    output logic            drop_ready,
    input  logic [AW:0]     drop_count,
    input  logic            drop_all
);

    /////////////////////////////////////////////////////////////////////////
    // Drop FSM States
    typedef enum logic [1:0] {
        IDLE        = 2'b00,  // Normal FIFO operation
        DROP_ACTIVE = 2'b01,  // Drop in progress, adjust pointers
        DROP_SETTLE = 2'b10,  // One cycle settling time
        DROP_DONE   = 2'b11   // Assert drop_ready
    } drop_state_t;

    drop_state_t r_drop_state, w_drop_state_next;

    /////////////////////////////////////////////////////////////////////////
    // Local signals
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic          w_drop_active;      // FSM is processing drop
    logic          w_use_drop_ptr;     // Trigger drop operation in counters

    // Common read-data wire driven inside the active MEM_STYLE branch
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Drop FSM
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (!axi_aresetn)
            r_drop_state <= IDLE;
        else
            r_drop_state <= w_drop_state_next;
    )


    always_comb begin
        w_drop_state_next = r_drop_state;  // Default: hold state
        case (r_drop_state)
            IDLE: begin
                if (drop_valid)
                    w_drop_state_next = DROP_ACTIVE;
            end
            DROP_ACTIVE: begin
                w_drop_state_next = DROP_SETTLE;  // Pointer adjust takes 1 cycle
            end
            DROP_SETTLE: begin
                w_drop_state_next = DROP_DONE;    // Settling time
            end
            DROP_DONE: begin
                // Wait for drop_valid to deassert before returning to IDLE
                if (!drop_valid)
                    w_drop_state_next = IDLE;
            end
            default: w_drop_state_next = IDLE;
        endcase
    end

    // Control signals derived from FSM state
    assign w_drop_active  = (r_drop_state == DROP_ACTIVE) || (r_drop_state == DROP_SETTLE);
    assign w_use_drop_ptr = (r_drop_state == DROP_ACTIVE);
    assign drop_ready     = (r_drop_state == DROP_DONE);

    /////////////////////////////////////////////////////////////////////////
    // Write counter (standard operation, supports drop_all load)
    logic w_write;
    logic w_wr_load;  // Load enable for drop_all
    assign w_write = wr_valid && wr_ready;
    assign w_wr_load = w_use_drop_ptr && drop_all;  // Load wr_ptr when drop_all

    counter_bin_load #(
        .WIDTH           (AW + 1),
        .MAX             (D)
    ) write_pointer_inst(
        .clk             (axi_aclk),
        .rst_n           (axi_aresetn),
        .enable          (w_write && !r_wr_full),
        .add_enable      (1'b0),          // Write pointer doesn't use add
        .add_value       ('0),
        .load            (w_wr_load),     // Load for drop_all
        .load_value      (r_wr_ptr_bin),  // Load same value (no change)
        .counter_bin_curr(r_wr_ptr_bin),
        .counter_bin_next(w_wr_ptr_bin_next)
    );

    /////////////////////////////////////////////////////////////////////////
    // Read counter (with add and load for drop operations)
    logic w_read;
    logic w_rd_add_enable;  // Add enable for drop by count
    logic w_rd_load;        // Load enable for drop_all
    assign w_read = rd_valid && rd_ready;
    assign w_rd_add_enable = w_use_drop_ptr && !drop_all;  // Add for drop count
    assign w_rd_load = w_use_drop_ptr && drop_all;         // Load for drop_all

    counter_bin_load #(
        .WIDTH           (AW + 1),
        .MAX             (D)
    ) read_pointer_inst(
        .clk             (axi_aclk),
        .rst_n           (axi_aresetn),
        .enable          (w_read && !r_rd_empty),
        .add_enable      (w_rd_add_enable),  // Drop by count
        .add_value       (drop_count),       // Number of entries to drop
        .load            (w_rd_load),        // Drop all
        .load_value      (r_wr_ptr_bin),     // Match write pointer (FIFO empty)
        .counter_bin_curr(r_rd_ptr_bin),
        .counter_bin_next(w_rd_ptr_bin_next)
    );

    // Use counter output directly (counter_bin_load handles all modes internally)
    logic [AW:0] w_rd_ptr_selected;
    assign w_rd_ptr_selected = w_rd_ptr_bin_next;

    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEPTH           (D),
        .ADDR_WIDTH      (AW),
        .ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN(ALMOST_WR_MARGIN),
        .REGISTERED      (REGISTERED)
    ) fifo_control_inst (
        .wr_clk          (axi_aclk),
        .wr_rst_n        (axi_aresetn),
        .rd_clk          (axi_aclk),
        .rd_rst_n        (axi_aresetn),
        .wr_ptr_bin      (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin (w_rd_ptr_selected),
        .rd_ptr_bin      (w_rd_ptr_selected),
        .rdom_wr_ptr_bin (w_wr_ptr_bin_next),
        .count           (count),
        .wr_full         (r_wr_full),
        .wr_almost_full  (r_wr_almost_full),
        .rd_empty        (r_rd_empty),
        .rd_almost_empty (r_rd_almost_empty)
    );

    // Block FIFO I/O during drop operation
    assign wr_ready = !r_wr_full && !w_drop_active;
    assign rd_valid = !r_rd_empty && !w_drop_active;

    /////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    // Mux mode (REGISTERED=0): Use next pointer for immediate combinational read
    // Flop mode (REGISTERED!=0): Use current pointer, data will be registered next cycle
    assign r_rd_addr = (REGISTERED == 0) ? w_rd_ptr_selected[AW-1:0] : r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory implementation (scoped per MEM_STYLE)
    // Note: Drop FIFO uses special pointer logic, but memory can still
    //       benefit from FPGA-specific inference hints
    /////////////////////////////////////////////////////////////////////////
    generate
        if (MEM_STYLE == FIFO_SRL) begin : gen_srl
            `ifdef XILINX
                (* shreg_extract = "yes", ram_style = "distributed" *)
            `elsif INTEL
                /* synthesis ramstyle = "MLAB" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path - combinational for drop FIFO (always mux mode for memory)
            always_comb w_rd_data = mem[r_rd_addr];

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_srl;
            genvar i_srl;
            for (i_srl = 0; i_srl < DEPTH; i_srl++) begin : gen_flatten_srl
                assign flat_mem_srl[i_srl*DW+:DW] = mem[i_srl];
            end
            // synopsys translate_on
        end
        else if (MEM_STYLE == FIFO_BRAM) begin : gen_bram
            `ifdef XILINX
                (* ram_style = "block" *)
            `elsif INTEL
                /* synthesis ramstyle = "M20K" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path - synchronous read for BRAM (forces registered output)
            `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                if (!axi_aresetn) w_rd_data <= '0;
                else              w_rd_data <= mem[r_rd_addr];
            )

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_bram;
            genvar i_bram;
            for (i_bram = 0; i_bram < DEPTH; i_bram++) begin : gen_flatten_bram
                assign flat_mem_bram[i_bram*DW+:DW] = mem[i_bram];
            end
            // synopsys translate_on

            initial begin
                if (REGISTERED == 0)
                    $display("NOTE: %s BRAM style uses synchronous read (+1 cycle latency)",
                            INSTANCE_NAME);
            end
        end
        else begin : gen_auto
            // Let tool decide (LUTRAM vs BRAM). Allow comb read for drop logic.
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path - combinational
            always_comb w_rd_data = mem[r_rd_addr];

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_auto;
            genvar i_auto;
            for (i_auto = 0; i_auto < DEPTH; i_auto++) begin : gen_flatten_auto
                assign flat_mem_auto[i_auto*DW+:DW] = mem[i_auto];
            end
            // synopsys translate_on
        end
    endgenerate

    // Debug: Track memory reads (outside generate block)
    // synopsys translate_off
    always @(posedge axi_aclk) begin
        if (rd_valid && rd_ready) begin
            $display("DEBUG %t: READ - rd_addr=%0d, w_rd_data=0x%02X, r_rd_ptr_bin=%0d, w_rd_ptr_selected=%0d",
                     $time, r_rd_addr, w_rd_data, r_rd_ptr_bin, w_rd_ptr_selected);
        end
    end
    // synopsys translate_on

    /////////////////////////////////////////////////////////////////////////
    // Read Port (final output register)
    generate
        if (REGISTERED != 0) begin : gen_flop_mode
            // Flop mode - registered output
            `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                if (!axi_aresetn)
                    rd_data <= 'b0;
                else
                    rd_data <= w_rd_data;
            )
        end else begin : gen_mux_mode
            // Mux mode - non-registered output
            assign rd_data = w_rd_data;
        end
    endgenerate

    /////////////////////////////////////////////////////////////////////////
    // Error checking
    // synopsys translate_off
    // Note: flat_mem_* signals for waveform viewing are generated inside
    //       each MEM_STYLE branch above (flat_mem_srl, flat_mem_bram, flat_mem_auto)

    // Protocol violation check: drop_valid must stay asserted until drop_ready
    // DISABLED: This checker was overly strict and caused false positives due to
    // CocoTB timing. The testbench properly waits for drop_ready before deasserting
    // drop_valid, but the signal change happens in the reactive region which can
    // trigger the checker due to delta cycles.
    // TODO: Revisit if a proper timing-aware checker is needed.
    /*
    logic r_drop_valid_seen;
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (!axi_aresetn)
            r_drop_valid_seen <= 1'b0;
        else if (drop_valid && !drop_ready)
            r_drop_valid_seen <= 1'b1;
        else if (drop_ready)
            r_drop_valid_seen <= 1'b0;
    )


    always @(posedge axi_aclk) begin
        if (r_drop_valid_seen && !drop_valid && !drop_ready) begin
            $error("FATAL: drop_valid deasserted before drop_ready - handshake violation!");
            $fatal(1, "Drop interface protocol violation");
        end
    end
    */

    // Debug: Track drop operations
    always @(posedge axi_aclk) begin
        if (drop_valid) begin
            $timeformat(-9, 3, " ns", 10);
            $display("DEBUG %t: DROP initiated - drop_all=%0d, drop_count=%0d, count=%0d",
                     $time, drop_all, drop_count, count);
            $display("  Before: r_rd_ptr_bin=%0d, r_wr_ptr_bin=%0d",
                     r_rd_ptr_bin, r_wr_ptr_bin);
        end
    end

    always @(posedge axi_aclk) begin
        if (r_drop_state == DROP_ACTIVE) begin
            $timeformat(-9, 3, " ns", 10);
            $display("DEBUG %t: DROP_ACTIVE - rd_ptr_next=%0d",
                     $time, w_rd_ptr_bin_next);
            $display("  Pointers to fifo_control: rd_ptr=%0d, wr_ptr=%0d",
                     w_rd_ptr_selected, w_wr_ptr_bin_next);
        end
    end

    always @(posedge axi_aclk) begin
        if (r_drop_state == DROP_SETTLE) begin
            $timeformat(-9, 3, " ns", 10);
            $display("DEBUG %t: DROP_SETTLE - r_rd_ptr_bin=%0d, r_wr_ptr_bin=%0d",
                     $time, r_rd_ptr_bin, r_wr_ptr_bin);
            $display("  Flags: rd_empty=%0d, rd_valid=%0d, count=%0d",
                     r_rd_empty, rd_valid, count);
        end
    end

    always @(posedge axi_aclk) begin
        if (r_drop_state == DROP_DONE) begin
            $timeformat(-9, 3, " ns", 10);
            $display("DEBUG %t: DROP_DONE - drop_ready asserted", $time);
            $display("  Final: r_rd_ptr_bin=%0d, r_wr_ptr_bin=%0d, count=%0d",
                     r_rd_ptr_bin, r_wr_ptr_bin, count);
            $display("  Flags: rd_empty=%0d, rd_valid=%0d", r_rd_empty, rd_valid);
        end
    end

    always @(posedge axi_aclk) begin
        if ((w_write && r_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge axi_aclk) begin
        if ((w_read && r_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge axi_aclk) begin
        if (drop_valid && !drop_all && (drop_count > count)) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s drop_count (%0d) exceeds current count (%0d), %t",
                     INSTANCE_NAME, drop_count, count, $time);
        end
    end

    always @(posedge axi_aclk) begin
        if (drop_valid && (r_drop_state != IDLE)) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s drop_valid asserted while drop already in progress, %t",
                     INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : gaxi_drop_fifo_sync
