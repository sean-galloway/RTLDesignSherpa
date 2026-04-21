// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_open_loop
// Purpose: Open-loop multi-bit CDC with synchronized enable pulse.
//
// The source domain holds data stable and asserts a single-cycle valid pulse.
// A sync_pulse synchronizer carries the valid indication to the destination
// domain, which latches the data on the synchronized pulse. No acknowledge
// path exists -- the source MUST guarantee that data remains stable for at
// least SYNC_STAGES + 1 destination clock cycles after asserting src_valid.
//
// This is the simplest vector CDC approach. It works well when:
//   - The source naturally holds data for many destination clocks
//     (e.g., fast source -> slow destination, or config register updates)
//   - Throughput is low (one transfer per ~6 destination clocks minimum)
//   - No backpressure is needed (destination always ready)
//
// For higher throughput or when the source cannot guarantee hold time,
// use cdc_2_phase_handshake (closed-loop) or fifo_async (streaming).
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
    input  logic [DATA_WIDTH-1:0] src_data,     // Data (must be stable for SYNC_STAGES+1 dst clocks)

    // Destination clock domain
    input  logic                  clk_dst,      // Destination domain clock
    input  logic                  rst_dst_n,    // Destination domain async reset (active low)
    output logic                  dst_valid,    // Single-cycle pulse: data latched
    output logic [DATA_WIDTH-1:0] dst_data      // Latched data (stable until next dst_valid)
);

    //=========================================================================
    // Source domain: hold data in a register
    //=========================================================================
    // The source asserts src_valid for one source clock cycle. We capture
    // the data into a holding register so it remains stable while the
    // valid pulse propagates through the synchronizer.

    logic [DATA_WIDTH-1:0] r_src_data;

    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_src_data <= '0;
        end else begin
            if (src_valid) begin
                r_src_data <= src_data;
            end
        end
    )

    //=========================================================================
    // Valid pulse synchronizer (source -> destination)
    //=========================================================================
    // sync_pulse converts a single-cycle source pulse into a single-cycle
    // destination pulse using toggle + edge detection. The data hold
    // register remains stable throughout this crossing.

    logic w_dst_valid_pulse;

    sync_pulse #(
        .SYNC_STAGES (SYNC_STAGES)
    ) u_sync_valid (
        .i_src_clk   (clk_src),
        .i_src_rst_n (rst_src_n),
        .i_src_pulse (src_valid),
        .i_dst_clk   (clk_dst),
        .i_dst_rst_n (rst_dst_n),
        .o_dst_pulse (w_dst_valid_pulse)
    );

    //=========================================================================
    // Destination domain: latch data on synchronized valid pulse
    //=========================================================================
    // When the synchronized valid pulse arrives, the source data has been
    // stable for SYNC_STAGES destination clock cycles (guaranteed by the
    // sync_pulse latency). We sample it into destination-domain registers.

    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            dst_data  <= '0;
            dst_valid <= 1'b0;
        end else begin
            dst_valid <= w_dst_valid_pulse;
            if (w_dst_valid_pulse) begin
                dst_data <= r_src_data;
            end
        end
    )

endmodule : cdc_open_loop
