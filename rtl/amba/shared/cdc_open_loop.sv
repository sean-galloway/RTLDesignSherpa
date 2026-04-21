// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_open_loop
// Purpose: Open-loop multi-bit CDC with synchronized enable pulse.
//
// The source asserts src_valid for one cycle (when !src_busy). Data is
// captured into a holding register and a toggle bit propagates through a
// forward synchronizer to the destination domain. The destination detects
// the toggle edge, latches the (now stable) data, and the toggle echoes
// back through a return synchronizer. When the source sees the echo,
// src_busy deasserts and the next transfer can proceed.
//
// "Open-loop" means the destination has no backpressure -- it always
// accepts. The return path exists only to protect the source from
// overwriting data before the destination has sampled it.
//
// This is the simplest vector CDC approach. It works well when:
//   - The destination is always ready (no flow control needed)
//   - Throughput is low (one transfer per ~2*SYNC_STAGES clocks)
//   - Configuration registers, status updates, infrequent events
//
// For destination-side backpressure, use cdc_2_phase_handshake.
// For streaming data, use fifo_async or gaxi_fifo_async.
//
// Documentation: docs/markdown/RTLAmba/shared/cdc_open_loop.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-04-21
//
// ===========================================================================
// REQUIRED SDC CONSTRAINTS
// ---------------------------------------------------------------------------
//   # 1. Valid pulse crossing (handled by sync_pulse internally)
//   set_max_delay -datapath_only \
//       -from [get_pins u_cdc_ol/u_sync_valid/r_src_toggle_reg/C] \
//       -to   [get_pins u_cdc_ol/u_sync_valid/r_dst_sync_reg[0]/D] \
//       <dst_period_ns>
//
//   # 2. Data bus (quasi-static, held by source for SYNC_STAGES+1 dst clocks)
//   set_max_delay -datapath_only \
//       -from [get_pins u_cdc_ol/r_src_data_reg[*]/C] \
//       -to   [get_pins u_cdc_ol/r_dst_data_reg[*]/D] \
//       <dst_period_ns>
//
// ===========================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cdc_open_loop #(
    parameter int DATA_WIDTH  = 8,   // Width of the data bus
    parameter int SYNC_STAGES = 3    // Synchronizer depth for valid pulse (2-4)
) (
    // Source clock domain
    input  logic                  clk_src,      // Source domain clock
    input  logic                  rst_src_n,    // Source domain async reset (active low)
    input  logic                  src_valid,    // Single-cycle pulse: data is valid NOW
    input  logic [DATA_WIDTH-1:0] src_data,     // Data from source domain
    output logic                  src_busy,     // High while transfer in flight (blocks next valid)

    // Destination clock domain
    input  logic                  clk_dst,      // Destination domain clock
    input  logic                  rst_dst_n,    // Destination domain async reset (active low)
    output logic                  dst_valid,    // Single-cycle pulse: data latched
    output logic [DATA_WIDTH-1:0] dst_data      // Latched data (stable until next dst_valid)
);

    //=========================================================================
    // Source domain: toggle-based request with busy protection
    //=========================================================================
    // On src_valid (when not busy), latch data and toggle the request bit.
    // The toggle propagates to the destination via a synchronizer, and a
    // return synchronizer brings it back. When the source sees its own
    // toggle echoed back, the destination has sampled the data and the
    // source is free to accept the next transfer.

    logic [DATA_WIDTH-1:0] r_src_data;
    logic r_src_toggle;

    // Accept valid only when not busy
    wire w_src_accept = src_valid && !src_busy;

    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_src_data   <= '0;
            r_src_toggle <= 1'b0;
        end else begin
            if (w_src_accept) begin
                r_src_data   <= src_data;
                r_src_toggle <= ~r_src_toggle;
            end
        end
    )

    //=========================================================================
    // Forward path: synchronize toggle to destination domain
    //=========================================================================

    logic w_dst_toggle_sync;

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (SYNC_STAGES),
        .WIDTH      (1)
    ) u_fwd_sync (
        .clk   (clk_dst),
        .rst_n (rst_dst_n),
        .d     (r_src_toggle),
        .q     (w_dst_toggle_sync)
    );

    //=========================================================================
    // Destination domain: edge detect and latch data
    //=========================================================================

    logic r_dst_toggle_prev;

    wire w_dst_event = w_dst_toggle_sync ^ r_dst_toggle_prev;

    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_dst_toggle_prev <= 1'b0;
            dst_data          <= '0;
            dst_valid         <= 1'b0;
        end else begin
            r_dst_toggle_prev <= w_dst_toggle_sync;
            dst_valid         <= w_dst_event;
            if (w_dst_event) begin
                dst_data <= r_src_data;
            end
        end
    )

    //=========================================================================
    // Return path: synchronize destination toggle back to source for busy
    //=========================================================================
    // When the source sees its toggle echoed back, the destination has
    // sampled the data. Until then, src_busy blocks new transfers.

    logic w_return_toggle_sync;

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (SYNC_STAGES),
        .WIDTH      (1)
    ) u_ret_sync (
        .clk   (clk_src),
        .rst_n (rst_src_n),
        .d     (w_dst_toggle_sync),
        .q     (w_return_toggle_sync)
    );

    // Busy when source toggle != returned (echoed) toggle
    assign src_busy = (r_src_toggle != w_return_toggle_sync);

endmodule : cdc_open_loop
