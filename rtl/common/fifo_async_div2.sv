// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: fifo_async_div2
// Purpose: //   Asynchronous FIFO with independent read and write clock domains. Uses
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: fifo_async_div2
//==============================================================================
// Description:
//   Asynchronous FIFO with independent read and write clock domains. Uses
//   Johnson counter (Gray code variant) for CDC-safe pointer synchronization.
//   Optimized for depths that are even numbers. Provides almost-full and
//   almost-empty flags for flow control.
//
// Features:
//   - Independent read/write clock domains (full CDC support)
//   - Johnson counter Gray code for pointer synchronization
//   - Configurable almost-full/almost-empty thresholds
//   - Optional registered output (mux or flop mode)
//   - Parameterized data width and depth
//   - Dual-port RAM implementation
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   REGISTERED:
//     Description: Output register mode
//     Type: int
//     Range: 0 or 1
//     Default: 0
//     Constraints: 0 = Mux mode (combinational read), 1 = Flop mode (registered read)
//
//   DATA_WIDTH:
//     Description: FIFO data path width in bits
//     Type: int
//     Range: 1 to 512
//     Default: 8
//     Constraints: Any positive integer
//
//   DEPTH:
//     Description: FIFO depth (number of entries)
//     Type: int
//     Range: 2 to 65536 (must be even for div2 optimization)
//     Default: 10
//     Constraints: Must be even number for Johnson counter operation
//
//   N_FLOP_CROSS:
//     Description: Number of synchronizer flops for CDC
//     Type: int
//     Range: 2 to 5
//     Default: 2
//     Constraints: 2 = minimum for metastability, 3+ for higher MTBF
//
//   ALMOST_WR_MARGIN:
//     Description: Almost-full threshold (entries from full)
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//     Constraints: wr_almost_full asserts when (used >= DEPTH - ALMOST_WR_MARGIN)
//
//   ALMOST_RD_MARGIN:
//     Description: Almost-empty threshold (entries from empty)
//     Type: int
//     Range: 1 to DEPTH-1
//     Default: 1
//     Constraints: rd_almost_empty asserts when (used <= ALMOST_RD_MARGIN)
//
//   INSTANCE_NAME:
//     Description: Instance name for debug/waveform identification
//     Type: string
//     Default: "DEADF1F0"
//     Constraints: String identifier (debugging only)
//
//   Derived Parameters (localparam - computed automatically):
//     DW: Alias for DATA_WIDTH
//     D: Alias for DEPTH
//     AW: Address width ($clog2(DEPTH))
//     JCW: Johnson Counter Width (same as DEPTH)
//     N: Alias for N_FLOP_CROSS
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Write Clock Domain:
//     wr_clk:           Write clock
//     wr_rst_n:         Write domain active-low reset
//     write:            Write enable
//     wr_data:          Write data input [DATA_WIDTH-1:0]
//     wr_full:          FIFO full flag (do not write when asserted)
//     wr_almost_full:   Almost-full warning flag
//
//   Read Clock Domain:
//     rd_clk:           Read clock
//     rd_rst_n:         Read domain active-low reset
//     read:             Read enable
//     rd_data:          Read data output [DATA_WIDTH-1:0]
//     rd_empty:         FIFO empty flag (do not read when asserted)
//     rd_almost_empty:  Almost-empty warning flag
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - DEPTH must be even for Johnson counter optimization
//   - Johnson counters provide Gray code properties for CDC safety
//   - N_FLOP_CROSS=2 is minimum; use 3+ for high-speed clock domain crossings
//   - ALMOST_* margins enable proactive flow control
//   - REGISTERED=1 adds one cycle read latency but improves timing
//   - Write when (!wr_full && write), read when (!rd_empty && read)
//   - Independent resets for write and read domains
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - fifo_async.sv - General async FIFO (any depth)
//   - fifo_sync.sv - Synchronous FIFO (single clock domain)
//   - counter_johnson.sv - Johnson counter (used internally)
//   - grayj2bin.sv - Johnson-to-binary converter (used internally)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_fifo_async_div2.py
//   Run: pytest val/common/test_fifo_async_div2.py -v
//
//==============================================================================
module fifo_async_div2 #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 10,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic                    wr_clk,
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

    localparam int DW = DATA_WIDTH;
    localparam int D = DEPTH;
    localparam int AW = $clog2(DEPTH);
    localparam int JCW = D;  // Johnson Counter Width
    localparam int N = N_FLOP_CROSS;

    /////////////////////////////////////////////////////////////////////////
    // local wires
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    // these are all based on the Johnson Counter
    logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    // The flop storage registers
    logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the binary counters for write and read pointers
    counter_bin #(
        .MAX                 (D),
        .WIDTH               (AW + 1)
    ) wr_ptr_counter_bin(
        .clk                 (wr_clk),
        .rst_n               (wr_rst_n),
        .enable              (write && !wr_full),
        .counter_bin_next    (w_wr_ptr_bin_next),
        .counter_bin_curr    (r_wr_ptr_bin)
    );

    counter_bin #(
        .MAX                 (D),
        .WIDTH               (AW + 1)
    ) rd_ptr_counter_bin(
        .clk                 (rd_clk),
        .rst_n               (rd_rst_n),
        .enable              (read && !rd_empty),
        .counter_bin_next    (w_rd_ptr_bin_next),
        .counter_bin_curr    (r_rd_ptr_bin)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the gray counters for write and read pointers
    counter_johnson #(
        .WIDTH               (JCW)
    ) wr_ptr_counter_gray(
        .clk                 (wr_clk),
        .rst_n               (wr_rst_n),
        .enable              (write && !wr_full),
        .counter_gray        (r_wr_ptr_gray)
    );

    counter_johnson #(
        .WIDTH               (JCW)
    ) rd_ptr_counter_gray(
        .clk                 (rd_clk),
        .rst_n               (rd_rst_n),
        .enable              (read && !rd_empty),
        .counter_gray        (r_rd_ptr_gray)
    );

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT          (N_FLOP_CROSS),
        .WIDTH               (JCW)
    ) rd_ptr_gray_cross_inst(
        .q                   (r_wdom_rd_ptr_gray),
        .d                   (r_rd_ptr_gray),
        .clk                 (wr_clk),
        .rst_n               (wr_rst_n)
    );

    // convert the gray rd ptr to binary
    grayj2bin #(
        .JCW                 (JCW),
        .WIDTH               (AW + 1),
        .INSTANCE_NAME       ("rd_ptr_johnson2bin_inst")
    ) rd_ptr_gray2bin_inst(
        .binary              (w_wdom_rd_ptr_bin),
        .gray                (r_wdom_rd_ptr_gray),
        .clk                 (wr_clk),
        .rst_n               (wr_rst_n)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT          (N_FLOP_CROSS),
        .WIDTH               (JCW)
    ) wr_ptr_gray_cross_inst(
        .q                   (r_rdom_wr_ptr_gray),
        .d                   (r_wr_ptr_gray),
        .clk                 (rd_clk),
        .rst_n               (rd_rst_n)
    );

    // convert the gray wr ptr to binary
    grayj2bin #(
        .JCW                 (JCW),
        .WIDTH               (AW + 1),
        .INSTANCE_NAME       ("wr_ptr_gray2bin_inst")
    ) wr_ptr_gray2bin_inst(
        .binary              (w_rdom_wr_ptr_bin),
        .gray                (r_rdom_wr_ptr_gray),
        .clk                 (rd_clk),
        .rst_n               (rd_rst_n)
    );

    /////////////////////////////////////////////////////////////////////////
    // assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge wr_clk) begin
        if (write) begin
            r_mem[r_wr_addr] <= wr_data;
        end
    end

    assign w_rd_data = r_mem[r_rd_addr];

    /////////////////////////////////////////////////////////////////////////
    // Read Port
    generate
        if (REGISTERED != 0) begin : gen_flop_mode
            // Flop mode - registered output
            always_ff @(posedge rd_clk or negedge rd_rst_n) begin
                if (!rd_rst_n)
                    rd_data <= 'b0;
                else
                    rd_data <= w_rd_data;
            end
        end else begin : gen_mux_mode
            // Mux mode - non-registered output
            assign rd_data = w_rd_data;
        end
    endgenerate

    /////////////////////////////////////////////////////////////////////////
    // Generate the Full/Empty signals
    fifo_control #(
        .DEPTH              (D),
        .ADDR_WIDTH         (AW),
        .ALMOST_RD_MARGIN   (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN   (ALMOST_WR_MARGIN),
        .REGISTERED         (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (wr_clk),
        .wr_rst_n         (wr_rst_n),
        .rd_clk           (rd_clk),
        .rd_rst_n         (rd_rst_n),
        .wr_ptr_bin      (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin (w_wdom_rd_ptr_bin),
        .rd_ptr_bin      (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin (w_rdom_wr_ptr_bin),
        .count           (),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

    /////////////////////////////////////////////////////////////////////////
    // Error checking and debug stuff
    // synopsys translate_off
    wire [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_flatten_memory
            assign flat_r_mem[i*DW+:DW] = r_mem[i];
        end
    endgenerate

    always_ff @(posedge wr_clk) begin
        if (!wr_rst_n && (write && wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always_ff @(posedge rd_clk) begin
        if (!wr_rst_n && (read && rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : fifo_async_div2
