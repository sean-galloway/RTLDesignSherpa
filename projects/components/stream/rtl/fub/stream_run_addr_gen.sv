// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_run_addr_gen
// Purpose:
//   TASK-101 (STREAM Extended) run-base address generator. Wraps one
//   dma_address_gen plus a run-base FIFO and produces the base address of each
//   *contiguous run* of an extended descriptor, buffered so the scheduler can
//   pull the next run's base the cycle it finishes the current run.
//
//   Run-contiguous model (chosen design):
//     - A transfer of `total_beats` is organized as runs of `inner_count`
//       contiguous beats. The AXI engine bursts within a run (stride_0 =
//       beat_size, handled by the engine's contiguous increment).
//     - This module emits one base per run for runs 1..num_runs-1 (run 0's base
//       is the descriptor src/dst address, used directly by the scheduler):
//           run_base(k) = base_addr + k * stride_1   (with optional wrap_1)
//       computed by dma_address_gen with index_0 = 0, index_1 = k.
//     - inner_count = 1 degrades to per-element addressing (scatter / transpose
//       write): every run is a single beat and index_1 walks every element.
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
    parameter int INDEX_WIDTH  = 16,   // run index / inner_count width
    parameter int FIFO_DEPTH   = 4,    // run-base prefetch depth
    parameter int BEATS_WIDTH  = 32    // total-beats / inner-count counter width
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // Start of a new (extended) descriptor: capture cfg and (re)arm generation.
    // Pulsed by the scheduler when the descriptor is loaded.
    input  logic                        start,

    // Per-descriptor configuration (sampled on `start`)
    input  logic [ADDR_WIDTH-1:0]       cfg_base_addr,    // run 0 base (src/dst addr)
    input  logic signed [STRIDE_WIDTH-1:0] cfg_stride_1,  // inter-run (outer) byte stride
    input  logic [ADDR_WIDTH-1:0]       cfg_wrap_mask_1,  // outer wrap mask (0 = none)
    input  logic [INDEX_WIDTH-1:0]      cfg_inner_count,  // contiguous beats per run (>=1)
    input  logic [BEATS_WIDTH-1:0]      cfg_total_beats,  // descriptor length in beats

    // Run-base output stream (runs 1..num_runs-1), consumed by the scheduler
    // at each run boundary.
    output logic                        o_base_valid,
    input  logic                        i_base_ready,
    output logic [ADDR_WIDTH-1:0]       o_base_addr
);

    //=========================================================================
    // Captured configuration
    //=========================================================================
    logic [ADDR_WIDTH-1:0]           r_base_addr;
    logic signed [STRIDE_WIDTH-1:0]  r_stride_1;
    logic [ADDR_WIDTH-1:0]           r_wrap_mask_1;
    logic [BEATS_WIDTH-1:0]          r_total_beats;
    logic [INDEX_WIDTH-1:0]          r_inner_count;

    // Run-index generator: index_1 = 1,2,... ; r_gen_beats accumulates the beats
    // already covered (run 0 covers the first inner_count). Generation stops once
    // r_gen_beats >= total_beats (all runs enumerated). Multiplier-free.
    logic [INDEX_WIDTH-1:0]          r_gen_index;    // next run index to request
    logic [BEATS_WIDTH-1:0]          r_gen_beats;    // beats covered by runs 0..r_gen_index-1
    logic                           r_gen_active;   // generation in progress

    logic w_more_runs;
    assign w_more_runs = r_gen_active && (r_gen_beats < r_total_beats);

    //=========================================================================
    // dma_address_gen request / result plumbing
    //=========================================================================
    logic                    w_req_valid, w_req_ready;
    logic                    w_res_valid, w_res_ready;
    logic [ADDR_WIDTH-1:0]   w_res_addr;

    // Request a base whenever more runs remain and the address generator can
    // accept it. index_0 = 0 (run base); index_1 = current run index.
    assign w_req_valid = w_more_runs;

    dma_address_gen #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .INDEX_WIDTH  (INDEX_WIDTH),
        .STRIDE_WIDTH (STRIDE_WIDTH),
        .TAG_WIDTH    (1)
    ) u_addr_gen (
        .i_clk            (clk),
        .i_rst_n          (rst_n),
        .i_cfg_base_addr  (r_base_addr),
        .i_cfg_stride_0   ('0),               // inner dim handled by engine burst
        .i_cfg_stride_1   (r_stride_1),
        .i_cfg_wrap_mask_0('0),
        .i_cfg_wrap_mask_1(r_wrap_mask_1),
        .i_req_valid      (w_req_valid),
        .o_req_ready      (w_req_ready),
        .i_req_index_0    ('0),
        .i_req_index_1    (r_gen_index),
        .i_req_tag        (1'b0),
        .o_result_valid   (w_res_valid),
        .i_result_ready   (w_res_ready),
        .o_result_addr    (w_res_addr),
        .o_result_tag     ()
    );

    // Advance the run index each time a request is accepted.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_base_addr   <= '0;
            r_stride_1    <= '0;
            r_wrap_mask_1 <= '0;
            r_total_beats <= '0;
            r_inner_count <= '0;
            r_gen_index   <= '0;
            r_gen_beats   <= '0;
            r_gen_active  <= 1'b0;
        end else if (start) begin
            // Capture cfg; run 0 is used directly by the scheduler, so generation
            // begins at run index 1 having already "covered" inner_count beats.
            r_base_addr   <= cfg_base_addr;
            r_stride_1    <= cfg_stride_1;
            r_wrap_mask_1 <= cfg_wrap_mask_1;
            r_total_beats <= cfg_total_beats;
            r_inner_count <= (cfg_inner_count == '0) ? INDEX_WIDTH'(1) : cfg_inner_count;
            r_gen_index   <= INDEX_WIDTH'(1);
            r_gen_beats   <= (cfg_inner_count == '0) ? BEATS_WIDTH'(1)
                                                     : BEATS_WIDTH'(cfg_inner_count);
            r_gen_active  <= 1'b1;
        end else begin
            if (w_req_valid && w_req_ready) begin
                r_gen_index <= r_gen_index + INDEX_WIDTH'(1);
                r_gen_beats <= r_gen_beats + BEATS_WIDTH'(r_inner_count);
            end
            // Deactivate once every run has been enumerated (last request issued).
            if (w_req_valid && w_req_ready &&
                (r_gen_beats + BEATS_WIDTH'(r_inner_count) >= r_total_beats)) begin
                r_gen_active <= 1'b0;
            end
        end
    )

    //=========================================================================
    // Run-base FIFO (prefetch generated bases ahead of consumption)
    //=========================================================================
    assign w_res_ready = 1'b1;  // FIFO write side accepts (depth sized for prefetch)

    gaxi_fifo_sync #(
        .DATA_WIDTH(ADDR_WIDTH),
        .DEPTH(FIFO_DEPTH)
    ) i_run_base_fifo (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (w_res_valid),
        .wr_ready    (),            // depth sized to hold all in-flight bases
        .wr_data     (w_res_addr),
        .rd_valid    (o_base_valid),
        .rd_ready    (i_base_ready),
        .rd_data     (o_base_addr),
        .count       ()
    );

endmodule : stream_run_addr_gen
