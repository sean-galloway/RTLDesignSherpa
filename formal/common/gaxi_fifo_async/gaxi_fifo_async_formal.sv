// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_fifo_async
// Purpose: Gaxi Fifo Async module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: gaxi_fifo_async (formal-friendly copy)
//==============================================================================
// Description:
//   Stripped copy of gaxi_fifo_async.sv for yosys formal verification.
//   Changes from original:
//     - Removed `include "fifo_defs.svh" (enum type not yosys-compatible)
//     - Removed parameter fifo_mem_t MEM_STYLE (replaced with AUTO branch only)
//     - Removed $timeformat/$display (not supported by yosys)
//     - Everything else identical to rtl/amba/gaxi/gaxi_fifo_async.sv
//==============================================================================

// fifo_defs.svh removed for yosys compatibility (fifo_mem_t enum)
`include "reset_defs.svh"


// Paramerized Asynchronous FIFO -- This works for any even depth
module gaxi_fifo_async #(
    parameter int        REGISTERED       = 0,   // 0 = mux mode, 1 = flop mode
    parameter int        DATA_WIDTH       = 8,
    parameter int        DEPTH            = 10,
    parameter int        N_FLOP_CROSS     = 2,
    parameter int        ALMOST_WR_MARGIN = 1,
    parameter int        ALMOST_RD_MARGIN = 1,
    parameter int        DW = DATA_WIDTH,
    parameter int        D  = DEPTH,
    parameter int        AW = $clog2(DEPTH),
    parameter int        JCW = D,   // Johnson Counter Width
    parameter int        N  = N_FLOP_CROSS
) (
    // clocks and resets
    input  logic            axi_wr_aclk,
                            axi_wr_aresetn,
                            axi_rd_aclk,
                            axi_rd_aresetn,
    // write side
    input  logic            wr_valid,
    output logic            wr_ready,   // not full
    input  logic [DW-1:0]   wr_data,
    // read side
    input  logic            rd_ready,
    output logic            rd_valid,   // not empty
    output logic [DW-1:0]   rd_data
);

    /////////////////////////////////////////////////////////////////////////
    // locals
    /////////////////////////////////////////////////////////////////////////
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    // Johnson/Gray domain pointers
    logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    // Binary pointers (+wrap bit)
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic        r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic        w_write, w_read;
    logic [AW:0] w_count;

    // Common read data; driven inside the selected memory branch
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // write/read enables
    /////////////////////////////////////////////////////////////////////////
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    /////////////////////////////////////////////////////////////////////////
    // Binary pointer counters (wr/rd domains)
    /////////////////////////////////////////////////////////////////////////
    counter_bin #(
        .MAX   (D),
        .WIDTH (AW + 1)
    ) wr_ptr_counter_bin(
        .clk              (axi_wr_aclk),
        .rst_n            (axi_wr_aresetn),
        .enable           (w_write && !r_wr_full),
        .counter_bin_next (w_wr_ptr_bin_next),
        .counter_bin_curr (r_wr_ptr_bin)
    );

    counter_bin #(
        .MAX   (D),
        .WIDTH (AW + 1)
    ) rd_ptr_counter_bin(
        .clk              (axi_rd_aclk),
        .rst_n            (axi_rd_aresetn),
        .enable           (w_read && !r_rd_empty),
        .counter_bin_next (w_rd_ptr_bin_next),
        .counter_bin_curr (r_rd_ptr_bin)
    );

    /////////////////////////////////////////////////////////////////////////
    // Johnson/Gray counters (wr/rd domains)
    /////////////////////////////////////////////////////////////////////////
    counter_johnson #(
        .WIDTH (JCW)
    ) wr_ptr_counter_gray(
        .clk          (axi_wr_aclk),
        .rst_n        (axi_wr_aresetn),
        .enable       (w_write && !r_wr_full),
        .counter_gray (r_wr_ptr_gray)
    );

    counter_johnson #(
        .WIDTH (JCW)
    ) rd_ptr_counter_gray(
        .clk          (axi_rd_aclk),
        .rst_n        (axi_rd_aresetn),
        .enable       (w_read && !r_rd_empty),
        .counter_gray (r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // CDC of Johnson/Gray pointers and conversion to binary
    /////////////////////////////////////////////////////////////////////////
    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (JCW)
    ) rd_ptr_gray_cross_inst(
        .q     (r_wdom_rd_ptr_gray),
        .d     (r_rd_ptr_gray),
        .clk   (axi_wr_aclk),
        .rst_n (axi_wr_aresetn)
    );

    grayj2bin #(
        .JCW           (JCW),
        .WIDTH         (AW + 1)
    ) rd_ptr_gray2bin_inst(
        .binary (w_wdom_rd_ptr_bin),
        .gray   (r_wdom_rd_ptr_gray),
        .clk    (axi_wr_aclk),
        .rst_n  (axi_wr_aresetn)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (JCW)
    ) wr_ptr_gray_cross_inst(
        .q     (r_rdom_wr_ptr_gray),
        .d     (r_wr_ptr_gray),
        .clk   (axi_rd_aclk),
        .rst_n (axi_rd_aresetn)
    );

    grayj2bin #(
        .JCW           (JCW),
        .WIDTH         (AW + 1)
    ) wr_ptr_gray2bin_inst(
        .binary (w_rdom_wr_ptr_bin),
        .gray   (r_rdom_wr_ptr_gray),
        .clk    (axi_rd_aclk),
        .rst_n  (axi_rd_aresetn)
    );

    /////////////////////////////////////////////////////////////////////////
    // address extraction
    /////////////////////////////////////////////////////////////////////////
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Full/empty/almost & count
    /////////////////////////////////////////////////////////////////////////
    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .REGISTERED        (REGISTERED)
    ) fifo_control_inst(
        .wr_clk            (axi_wr_aclk),
        .wr_rst_n          (axi_wr_aresetn),
        .rd_clk            (axi_rd_aclk),
        .rd_rst_n          (axi_rd_aresetn),
        .wr_ptr_bin        (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin   (w_wdom_rd_ptr_bin),
        .rd_ptr_bin        (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin   (w_rdom_wr_ptr_bin),
        .wr_full           (r_wr_full),
        .wr_almost_full    (r_wr_almost_full),
        .rd_empty          (r_rd_empty),
        .rd_almost_empty   (r_rd_almost_empty),
        .count             (w_count)
    );

    assign wr_ready = !r_wr_full;
    assign rd_valid = !r_rd_empty;

    /////////////////////////////////////////////////////////////////////////
    // Memory implementation (MEM_STYLE removed for yosys -- using auto/inferred)
    /////////////////////////////////////////////////////////////////////////
    logic [DATA_WIDTH-1:0] mem [DEPTH];

    // Write port (axi_wr_aclk)
    always_ff @(posedge axi_wr_aclk) begin
        if (w_write && !r_wr_full) begin
            mem[r_wr_addr] <= wr_data;
        end
    end

    generate
        if (REGISTERED != 0) begin : g_flop
            `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
                if (!axi_rd_aresetn) w_rd_data <= '0;
                else                 w_rd_data <= mem[r_rd_addr];
            )

        end else begin : g_mux
            always_comb w_rd_data = mem[r_rd_addr];
        end
    endgenerate

    // Common output connect
    assign rd_data = w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Overflow/underflow error checking
    /////////////////////////////////////////////////////////////////////////
    // (removed for formal)

endmodule : gaxi_fifo_async
