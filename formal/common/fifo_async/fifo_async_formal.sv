// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: fifo_async
// Purpose: //   Asynchronous FIFO for safe clock domain crossing (CDC) between independent
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: fifo_async (formal-friendly copy)
//==============================================================================
// Description:
//   Stripped copy of fifo_async.sv for yosys formal verification.
//   Changes from original:
//     - Removed `include "fifo_defs.svh" (enum type not yosys-compatible)
//     - Removed parameter fifo_mem_t MEM_STYLE (replaced with hardcoded 0)
//     - Removed $timeformat/$display (not supported by yosys)
//     - Everything else identical to rtl/common/fifo_async.sv
//==============================================================================

`include "reset_defs.svh"


module fifo_async #(
    parameter int  REGISTERED      = 0,   // 0 = mux (combinational read), 1 = flop (registered read)
    parameter int  DATA_WIDTH      = 8,
    parameter int  DEPTH           = 16,
    parameter int  N_FLOP_CROSS    = 2,
    parameter int  ALMOST_WR_MARGIN= 1,
    parameter int  ALMOST_RD_MARGIN= 1
) (
    // clocks and resets
    input  logic wr_clk,
                wr_rst_n,
                rd_clk,
                rd_rst_n,

    // wr_clk domain
    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,

    // rd_clk domain
    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    // -----------------------------------------------------------------------
    // Derived params / locals
    // -----------------------------------------------------------------------
    localparam int DW = DATA_WIDTH;
    localparam int D  = DEPTH;
    localparam int AW = $clog2(DEPTH);
    localparam int N  = N_FLOP_CROSS;

    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_gray, r_wdom_rd_ptr_gray;
    logic [AW:0]   r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0]   r_wr_ptr_bin,  r_rd_ptr_bin;
    logic [AW:0]   w_wdom_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // Common read-data line; driven inside the active memory branch
    logic [DW-1:0] w_rd_data;

    // -----------------------------------------------------------------------
    // Write/read pointer generation (bin+gray)
    // -----------------------------------------------------------------------
    counter_bingray #(
        .WIDTH (AW + 1)
    ) wr_ptr_counter_gray (
        .clk           (wr_clk),
        .rst_n         (wr_rst_n),
        .enable        (write && !wr_full),
        .counter_bin   (r_wr_ptr_bin),
        .counter_bin_next (w_wr_ptr_bin_next),
        .counter_gray  (r_wr_ptr_gray)
    );

    counter_bingray #(
        .WIDTH (AW + 1)
    ) rd_ptr_counter_gray (
        .clk           (rd_clk),
        .rst_n         (rd_rst_n),
        .enable        (read && !rd_empty),
        .counter_bin   (r_rd_ptr_bin),
        .counter_bin_next (w_rd_ptr_bin_next),
        .counter_gray  (r_rd_ptr_gray)
    );

    // -----------------------------------------------------------------------
    // CDC of gray pointers (wr<->rd domains) + gray->bin
    // -----------------------------------------------------------------------
    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (AW + 1)
    ) rd_ptr_gray_cross_inst (
        .q     (r_wdom_rd_ptr_gray),
        .d     (r_rd_ptr_gray),
        .clk   (wr_clk),
        .rst_n (wr_rst_n)
    );

    gray2bin #(
        .WIDTH (AW + 1)
    ) rd_ptr_gray2bin_inst (
        .binary (w_wdom_rd_ptr_bin),
        .gray   (r_wdom_rd_ptr_gray)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (AW + 1)
    ) wr_ptr_gray_cross_inst (
        .q     (r_rdom_wr_ptr_gray),
        .d     (r_wr_ptr_gray),
        .clk   (rd_clk),
        .rst_n (rd_rst_n)
    );

    gray2bin #(
        .WIDTH (AW + 1)
    ) wr_ptr_gray2bin_inst (
        .binary (w_rdom_wr_ptr_bin),
        .gray   (r_rdom_wr_ptr_gray)
    );

    // -----------------------------------------------------------------------
    // Address extraction (lower bits from binary pointers)
    // -----------------------------------------------------------------------
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    // -----------------------------------------------------------------------
    // Full/empty/almost flags (shared control)
    // -----------------------------------------------------------------------
    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .REGISTERED        (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (wr_clk),
        .wr_rst_n         (wr_rst_n),
        .rd_clk           (rd_clk),
        .rd_rst_n         (rd_rst_n),

        .wr_ptr_bin       (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin  (w_wdom_rd_ptr_bin),
        .rd_ptr_bin       (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin  (w_rdom_wr_ptr_bin),

        .count            (),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

    // -----------------------------------------------------------------------
    // Memory implementation (MEM_STYLE hardcoded to FIFO_AUTO = 0)
    // NOTE:
    //   * SRL/AUTO branches can support combinational read (REGISTERED=0).
    //   * BRAM branch uses synchronous read on rd_clk to infer true dual-port
    //     block RAM. That implies +1 cycle latency; if REGISTERED=0, behavior
    //     becomes effectively registered in this branch.
    // -----------------------------------------------------------------------
    generate
        // MEM_STYLE == 0 (FIFO_AUTO): gen_auto branch only
        begin : gen_auto
            // Tool chooses resource; allow async read when REGISTERED==0
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write port (wr_clk)
            always_ff @(posedge wr_clk) begin
                if (write && !wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            if (REGISTERED != 0) begin : g_flop
                // Registered read (rd_clk)
                `ALWAYS_FF_RST(rd_clk, rd_rst_n,
                    if (!rd_rst_n) w_rd_data <= '0;
                    else           w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                // Combinational read (may infer LUTRAM)
                always_comb w_rd_data = mem[r_rd_addr];
            end

        end
    endgenerate

    // -----------------------------------------------------------------------
    // Output connect (common)
    // -----------------------------------------------------------------------
    assign rd_data = w_rd_data;

    // -----------------------------------------------------------------------
    // Overflow/underflow error checking
    // -----------------------------------------------------------------------
    // Simulation-only overflow/underflow checks removed for formal
    // (original uses $timeformat/$display which yosys does not support)

endmodule : fifo_async
