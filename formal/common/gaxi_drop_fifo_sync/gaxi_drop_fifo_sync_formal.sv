// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_drop_fifo_sync
// Purpose: Synchronous FIFO with dynamic drop capability (formal-friendly copy)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: gaxi_drop_fifo_sync (formal-friendly copy)
//==============================================================================
// Description:
//   Stripped copy of gaxi_drop_fifo_sync.sv for yosys formal verification.
//   Changes from original:
//     - Removed `include "fifo_defs.svh" (enum type not yosys-compatible)
//     - Removed parameter fifo_mem_t MEM_STYLE (replaced with AUTO branch only)
//     - Removed $timeformat/$display (not supported by yosys)
//     - Everything else identical to rtl/amba/gaxi/gaxi_drop_fifo_sync.sv
//==============================================================================

// fifo_defs.svh removed for yosys compatibility (fifo_mem_t enum)
`include "reset_defs.svh"


module gaxi_drop_fifo_sync #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
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
            // verilator coverage_off
            // DEFENSIVE: Illegal FSM state recovery
            default: w_drop_state_next = IDLE;
            // verilator coverage_on
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
    // Memory implementation (MEM_STYLE removed for yosys -- using auto/inferred)
    /////////////////////////////////////////////////////////////////////////
    logic [DATA_WIDTH-1:0] mem [DEPTH];

    // Write path
    always_ff @(posedge axi_aclk) begin
        if (w_write && !r_wr_full) begin
            mem[r_wr_addr] <= wr_data;
        end
    end

    // Read path - combinational
    always_comb w_rd_data = mem[r_rd_addr];

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
    // Overflow/underflow and protocol error checking
    /////////////////////////////////////////////////////////////////////////
    // (removed for formal)

endmodule : gaxi_drop_fifo_sync
