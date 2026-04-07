// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible copy of fifo_async_div2.sv for formal verification.
// Changes from original:
//   - Removed `include "fifo_defs.svh" (enum type not yosys-compatible)
//   - Removed parameter fifo_mem_t MEM_STYLE (hardcoded to AUTO=0 branch)
//   - Removed `include "reset_defs.svh" (inlined at top)
//   - Everything else identical to rtl/common/fifo_async_div2.sv

`include "reset_defs.svh"

module fifo_async_div2 #(
    parameter int    REGISTERED        = 0,
    parameter int    DATA_WIDTH        = 8,
    parameter int    DEPTH             = 10,
    parameter int    N_FLOP_CROSS      = 2,
    parameter int    ALMOST_WR_MARGIN  = 1,
    parameter int    ALMOST_RD_MARGIN  = 1
) (
    input  logic wr_clk,
                wr_rst_n,
                rd_clk,
                rd_rst_n,

    input  logic                    write,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    wr_full,
    output logic                    wr_almost_full,

    input  logic                    read,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    localparam int DW  = DATA_WIDTH;
    localparam int D   = DEPTH;
    localparam int AW  = $clog2(DEPTH);
    localparam int JCW = D;
    localparam int N   = N_FLOP_CROSS;

    logic [AW-1:0] r_wr_addr, r_rd_addr;

    logic [JCW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray;
    logic [JCW-1:0] r_rd_ptr_gray, r_rdom_wr_ptr_gray;

    logic [AW:0] r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0] w_wdom_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;

    logic [DW-1:0] w_rd_data;

    // Binary pointer counters
    counter_bin #(
        .MAX   (D),
        .WIDTH (AW + 1)
    ) wr_ptr_counter_bin (
        .clk              (wr_clk),
        .rst_n            (wr_rst_n),
        .enable           (write && !wr_full),
        .counter_bin_next (w_wr_ptr_bin_next),
        .counter_bin_curr (r_wr_ptr_bin)
    );

    counter_bin #(
        .MAX   (D),
        .WIDTH (AW + 1)
    ) rd_ptr_counter_bin (
        .clk              (rd_clk),
        .rst_n            (rd_rst_n),
        .enable           (read && !rd_empty),
        .counter_bin_next (w_rd_ptr_bin_next),
        .counter_bin_curr (r_rd_ptr_bin)
    );

    // Johnson/Gray counters
    counter_johnson #(
        .WIDTH (JCW)
    ) wr_ptr_counter_gray (
        .clk          (wr_clk),
        .rst_n        (wr_rst_n),
        .enable       (write && !wr_full),
        .counter_gray (r_wr_ptr_gray)
    );

    counter_johnson #(
        .WIDTH (JCW)
    ) rd_ptr_counter_gray (
        .clk          (rd_clk),
        .rst_n        (rd_rst_n),
        .enable       (read && !rd_empty),
        .counter_gray (r_rd_ptr_gray)
    );

    // CDC of Johnson/Gray pointers and conversion to binary
    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (JCW)
    ) rd_ptr_gray_cross_inst (
        .q     (r_wdom_rd_ptr_gray),
        .d     (r_rd_ptr_gray),
        .clk   (wr_clk),
        .rst_n (wr_rst_n)
    );

    grayj2bin #(
        .JCW           (JCW),
        .WIDTH         (AW + 1)
    ) rd_ptr_gray2bin_inst (
        .binary (w_wdom_rd_ptr_bin),
        .gray   (r_wdom_rd_ptr_gray),
        .clk    (wr_clk),
        .rst_n  (wr_rst_n)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (JCW)
    ) wr_ptr_gray_cross_inst (
        .q     (r_rdom_wr_ptr_gray),
        .d     (r_wr_ptr_gray),
        .clk   (rd_clk),
        .rst_n (rd_rst_n)
    );

    grayj2bin #(
        .JCW           (JCW),
        .WIDTH         (AW + 1)
    ) wr_ptr_gray2bin_inst (
        .binary (w_rdom_wr_ptr_bin),
        .gray   (r_rdom_wr_ptr_gray),
        .clk    (rd_clk),
        .rst_n  (rd_rst_n)
    );

    // Address extraction
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    // Flag/control logic
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

    // Memory implementation (FIFO_AUTO, allow comb read when REGISTERED==0)
    generate
        begin : gen_auto
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            always_ff @(posedge wr_clk) begin
                if (write && !wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            if (REGISTERED != 0) begin : g_flop
                always @(posedge rd_clk or negedge rd_rst_n) begin
                    if (!rd_rst_n) w_rd_data <= '0;
                    else           w_rd_data <= mem[r_rd_addr];
                end
            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end
        end
    endgenerate

    assign rd_data = w_rd_data;

endmodule : fifo_async_div2
