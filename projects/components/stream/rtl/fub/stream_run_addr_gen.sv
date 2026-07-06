// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_run_addr_gen
// Purpose:
//   TASK-101 (STREAM Extended) address generator. Wraps one dma_address_gen plus
//   a base FIFO and produces the sequence of addresses the scheduler consumes,
//   in one of two per-direction modes:
//
//   RUN-CONTIGUOUS (per_beat = 0, stride_0 == beat_size):
//     A transfer of `total_beats` is organized as runs of `inner_count`
//     contiguous beats; the AXI engine bursts within a run. This module emits
//     one base per run for runs 1..N-1 (run 0's base = descriptor addr, used
//     directly by the scheduler):
//         run_base(k) = base + k * stride_1        (index_0 = 0, index_1 = k)
//     Efficient for linear / 2D-tiled contiguous / circular / reverse copies.
//
//   PER-BEAT 2-D (per_beat = 1, stride_0 != beat_size):
//     Every beat has its own address (single-beat AXI on this side). Used for
//     transpose / arbitrary scatter, where the inner dimension is itself strided
//     so there is no contiguous run to burst. Emits every beat 1..total-1:
//         addr(b) = base + i0*stride_0 + i1*stride_1,
//         with i0 = b % inner_count (inner, fastest), i1 = b / inner_count.
//     The scheduler drives sched_*_beats = 1 for a per-beat direction.
//
//   Read and write use independent instances, so a transpose reads with bursts
//   (contiguous side) and writes single-beat (strided side), or vice versa.
//
// Documentation: projects/components/stream/TASKS.md (TASK-101)
// Subsystem: stream
//
// Author: sean galloway
// Created: 2026-07-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_run_addr_gen #(
    parameter int ADDR_WIDTH   = 64,
    parameter int STRIDE_WIDTH = 32,   // signed byte stride
    parameter int INDEX_WIDTH  = 16,   // dimension index / inner_count width
    parameter int FIFO_DEPTH   = 4,    // address prefetch depth
    parameter int BEATS_WIDTH  = 32    // total-beats / inner-count counter width
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // Start of a new (extended) descriptor: capture cfg and (re)arm generation.
    input  logic                        start,

    // Per-descriptor configuration (sampled on `start`)
    input  logic                        cfg_per_beat,     // 1 = per-beat 2-D, 0 = run-contiguous
    input  logic [ADDR_WIDTH-1:0]       cfg_base_addr,    // beat/run 0 base (src/dst addr)
    input  logic signed [STRIDE_WIDTH-1:0] cfg_stride_0,  // inner (index_0) byte stride
    input  logic signed [STRIDE_WIDTH-1:0] cfg_stride_1,  // outer (index_1) byte stride
    input  logic [ADDR_WIDTH-1:0]       cfg_wrap_mask_0,  // inner wrap mask (0 = none)
    input  logic [ADDR_WIDTH-1:0]       cfg_wrap_mask_1,  // outer wrap mask (0 = none)
    input  logic [INDEX_WIDTH-1:0]      cfg_inner_count,  // index_0 extent (>=1)
    input  logic [BEATS_WIDTH-1:0]      cfg_total_beats,  // descriptor length in beats

    // Address output stream (positions 1..N-1), consumed by the scheduler at
    // each run/beat boundary.
    output logic                        o_base_valid,
    input  logic                        i_base_ready,
    output logic [ADDR_WIDTH-1:0]       o_base_addr
);

    //=========================================================================
    // Captured configuration
    //=========================================================================
    logic                            r_per_beat;
    logic [ADDR_WIDTH-1:0]           r_base_addr;
    logic signed [STRIDE_WIDTH-1:0]  r_stride_0;
    logic signed [STRIDE_WIDTH-1:0]  r_stride_1;
    logic [ADDR_WIDTH-1:0]           r_wrap_mask_0;
    logic [ADDR_WIDTH-1:0]           r_wrap_mask_1;
    logic [BEATS_WIDTH-1:0]          r_total_beats;
    logic [INDEX_WIDTH-1:0]          r_inner_count;

    // Dimension index counters (i0 = inner/fastest, i1 = outer) and the
    // beats-covered accumulator that terminates generation. Multiplier-free.
    logic [INDEX_WIDTH-1:0]          r_i0, r_i1;
    logic [BEATS_WIDTH-1:0]          r_gen_beats;   // beats covered by positions 0..current-1
    logic                           r_gen_active;

    // Guarded inner_count for the start branch (0 -> 1).
    logic [INDEX_WIDTH-1:0]          w_start_inner;
    assign w_start_inner = (cfg_inner_count == '0) ? INDEX_WIDTH'(1) : cfg_inner_count;

    // Beats advanced per generated position: 1 (per-beat) or inner_count (run).
    logic [BEATS_WIDTH-1:0]          w_step;
    assign w_step = r_per_beat ? BEATS_WIDTH'(1) : BEATS_WIDTH'(r_inner_count);

    // More positions to enumerate while covered beats < total.
    logic w_more;
    assign w_more = r_gen_active && (r_gen_beats < r_total_beats);

    //=========================================================================
    // dma_address_gen request / result plumbing
    //=========================================================================
    logic                    w_req_valid, w_req_ready;
    logic                    w_res_valid, w_res_ready;
    logic [ADDR_WIDTH-1:0]   w_res_addr;

    assign w_req_valid = w_more;

    dma_address_gen #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .INDEX_WIDTH  (INDEX_WIDTH),
        .STRIDE_WIDTH (STRIDE_WIDTH),
        .TAG_WIDTH    (1)
    ) u_addr_gen (
        .i_clk            (clk),
        .i_rst_n          (rst_n),
        .i_cfg_base_addr  (r_base_addr),
        .i_cfg_stride_0   (r_stride_0),
        .i_cfg_stride_1   (r_stride_1),
        .i_cfg_wrap_mask_0(r_wrap_mask_0),
        .i_cfg_wrap_mask_1(r_wrap_mask_1),
        .i_req_valid      (w_req_valid),
        .o_req_ready      (w_req_ready),
        .i_req_index_0    (r_i0),
        .i_req_index_1    (r_i1),
        .i_req_tag        (1'b0),
        .o_result_valid   (w_res_valid),
        .i_result_ready   (w_res_ready),
        .o_result_addr    (w_res_addr),
        .o_result_tag     ()
    );

    //=========================================================================
    // Index / termination generation
    //=========================================================================
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_per_beat    <= 1'b0;
            r_base_addr   <= '0;
            r_stride_0    <= '0;
            r_stride_1    <= '0;
            r_wrap_mask_0 <= '0;
            r_wrap_mask_1 <= '0;
            r_total_beats <= '0;
            r_inner_count <= INDEX_WIDTH'(1);
            r_i0          <= '0;
            r_i1          <= '0;
            r_gen_beats   <= '0;
            r_gen_active  <= 1'b0;
        end else if (start) begin
            // Capture cfg. Position 0 (beat/run 0) is used directly by the
            // scheduler, so generation begins at position 1.
            r_per_beat    <= cfg_per_beat;
            r_base_addr   <= cfg_base_addr;
            r_stride_0    <= cfg_stride_0;
            r_stride_1    <= cfg_stride_1;
            r_wrap_mask_0 <= cfg_wrap_mask_0;
            r_wrap_mask_1 <= cfg_wrap_mask_1;
            r_total_beats <= cfg_total_beats;
            r_inner_count <= w_start_inner;
            r_gen_active  <= 1'b1;
            if (cfg_per_beat) begin
                // Beat 1: inner index advances fastest.
                r_gen_beats <= BEATS_WIDTH'(1);              // beat 0 covered
                if (w_start_inner > INDEX_WIDTH'(1)) begin
                    r_i0 <= INDEX_WIDTH'(1);
                    r_i1 <= '0;
                end else begin                                // inner_count == 1
                    r_i0 <= '0;
                    r_i1 <= INDEX_WIDTH'(1);
                end
            end else begin
                // Run 1: only the outer index advances.
                r_gen_beats <= BEATS_WIDTH'(w_start_inner);   // run 0 covered
                r_i0 <= '0;
                r_i1 <= INDEX_WIDTH'(1);
            end
        end else if (w_req_valid && w_req_ready) begin
            r_gen_beats <= r_gen_beats + w_step;
            if (r_per_beat) begin
                // 2-D walk: inner fastest, carry into outer.
                if (r_i0 == (r_inner_count - INDEX_WIDTH'(1))) begin
                    r_i0 <= '0;
                    r_i1 <= r_i1 + INDEX_WIDTH'(1);
                end else begin
                    r_i0 <= r_i0 + INDEX_WIDTH'(1);
                end
            end else begin
                // 1-D walk: outer only (run bases).
                r_i1 <= r_i1 + INDEX_WIDTH'(1);
            end
        end
    )

    //=========================================================================
    // Address FIFO (prefetch generated addresses ahead of consumption)
    //=========================================================================
    // The addr-gen result interface MUST backpressure on the FIFO's wr_ready:
    // otherwise, when the FIFO fills (consumer slower than the 1/cycle generator)
    // the addr-gen would advance its index while its output is dropped, losing
    // addresses and desyncing (underrun/hang). Feeding wr_ready to i_result_ready
    // stalls generation until the FIFO drains.
    logic w_fifo_wr_ready;
    assign w_res_ready = w_fifo_wr_ready;

    gaxi_fifo_sync #(
        .DATA_WIDTH(ADDR_WIDTH),
        .DEPTH(FIFO_DEPTH)
    ) i_addr_fifo (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (w_res_valid),
        .wr_ready    (w_fifo_wr_ready),
        .wr_data     (w_res_addr),
        .rd_valid    (o_base_valid),
        .rd_ready    (i_base_ready),
        .rd_data     (o_base_addr),
        .count       ()
    );

endmodule : stream_run_addr_gen
