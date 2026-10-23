// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_g_base_fifo
// Purpose: EXT run-base queue between the gatling firmware and one
//          scheduler_g direction (rapids TASK-034).  The firmware writes a
//          64-bit base as two 32-bit words: LO is held, the HI write pushes
//          {HI, LO}.  `flush` empties it in one cycle -- scheduler_g holds it
//          flushed outside FETCH_DESC / XFER_DATA, so a base left over from
//          a reset or an errored descriptor never reaches the next one.  A
//          push while full is dropped and reported on `drop` (one cycle).
//
// Parameters:
//   - ADDR_WIDTH: base width, <= 64 (the HI word's upper bits are dropped)
//   - DEPTH: entries, 2..8 (scheduler_g uses 4, the depth of
//            stream_run_addr_gen's own FIFO)
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scheduler_g_base_fifo #(
    parameter int ADDR_WIDTH = 64,
    parameter int DEPTH      = 4,
    parameter int CNT_W      = $clog2(DEPTH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    input  logic                    flush,
    input  logic                    lo_wr,
    input  logic                    hi_wr,      // pushes {wr_data, held LO}
    input  logic [31:0]             wr_data,
    output logic                    drop,       // push while full
    output logic [CNT_W-1:0]        count,

    output logic                    rd_valid,
    input  logic                    rd_ready,
    output logic [ADDR_WIDTH-1:0]   rd_addr
);

    localparam int PTR_W = (DEPTH > 1) ? $clog2(DEPTH) : 1;

    initial begin
        if ((DEPTH < 2) || (DEPTH > 8))
            $fatal(1, "scheduler_g_base_fifo: DEPTH must be 2..8, got %0d", DEPTH);
        if (ADDR_WIDTH > 64)
            $fatal(1, "scheduler_g_base_fifo: ADDR_WIDTH must be <= 64, got %0d", ADDR_WIDTH);
    end

    logic [31:0]           r_lo;
    logic [ADDR_WIDTH-1:0] r_mem [DEPTH];
    logic [PTR_W-1:0]      r_wr_ptr, r_rd_ptr;
    logic [CNT_W-1:0]      r_count;

    wire w_full = (r_count == CNT_W'(DEPTH));
    wire w_push = hi_wr && !w_full && !flush;
    wire w_pop  = rd_valid && rd_ready && !flush;

    function automatic logic [PTR_W-1:0] ptr_inc(input logic [PTR_W-1:0] p);
        return (p == PTR_W'(DEPTH - 1)) ? '0 : p + PTR_W'(1);
    endfunction

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_lo     <= 32'h0;
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
            r_count  <= '0;
        end else if (flush) begin
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
            r_count  <= '0;
        end else begin
            if (lo_wr)  r_lo     <= wr_data;
            if (w_push) r_wr_ptr <= ptr_inc(r_wr_ptr);
            if (w_pop)  r_rd_ptr <= ptr_inc(r_rd_ptr);
            r_count <= r_count + CNT_W'(w_push) - CNT_W'(w_pop);
        end
    )

    // Storage: no reset (an empty entry is never read)
    always_ff @(posedge clk) begin
        if (w_push) r_mem[r_wr_ptr] <= ADDR_WIDTH'({wr_data, r_lo});
    end

    assign drop     = hi_wr && w_full && !flush;
    assign count    = r_count;
    assign rd_valid = (r_count != '0);
    assign rd_addr  = r_mem[r_rd_ptr];

endmodule : scheduler_g_base_fifo
