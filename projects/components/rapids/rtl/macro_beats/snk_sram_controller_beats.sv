// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: snk_sram_controller
// Purpose: Multi-channel Sink SRAM Controller
//
// Description:
//   Multi-channel SRAM controller for the SINK path using per-channel FIFOs
//   with latency bridge. Supports up to 128 channels.
//
//   Data flow: Network Slave (fill) -> SRAM -> AXI Write Engine (drain)
//
// Architecture:
//   - Fill Path: Network Slave -> Allocation Controller -> FIFO
//   - Drain Path: FIFO -> Latency Bridge -> AXI Write Engine
//   - Per-channel space tracking and data counting
//   - ID-based channel routing (supports up to 128 channels)
//
// Key Features:
//   - Independent FIFO per channel (no segmentation complexity)
//   - Allocation controller tracks reserved vs. committed space
//   - Latency bridge aligns FIFO read latency (registered output)
//   - Saturating segment count reporting
//
// Subsystem: rapids_macro_beats
//
// Author: RTL Design Sherpa
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module snk_sram_controller_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int DW = DATA_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    // Channel ID width: supports up to 128 channels (7 bits)
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Fill Allocation Interface (Network Slave -> SRAM)
    // Single request with ID - ID selects which channel's space to check
    //=========================================================================
    input  logic                        fill_alloc_req,
    input  logic [7:0]                  fill_alloc_size,
    input  logic [CIW-1:0]              fill_alloc_id,
    output logic [NC-1:0][SCW-1:0]      fill_space_free,

    //=========================================================================
    // Fill Data Interface (Network Slave -> FIFO)
    // Transaction ID-based: single valid + ID selects channel
    //=========================================================================
    input  logic                        fill_valid,
    output logic                        fill_ready,
    input  logic [CIW-1:0]              fill_id,
    input  logic [DW-1:0]               fill_data,

    //=========================================================================
    // Drain Flow Control Interface (AXI Write Engine)
    //=========================================================================
    output logic [NC-1:0][SCW-1:0]      drain_data_avail,
    input  logic [NC-1:0]               drain_req,
    input  logic [NC-1:0][7:0]          drain_size,

    //=========================================================================
    // Drain Data Interface (FIFO -> AXI Write Engine)
    //=========================================================================
    output logic [NC-1:0]               drain_valid,
    input  logic                        drain_read,
    input  logic [CIW-1:0]              drain_id,
    output logic [DW-1:0]               drain_data,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_bridge_pending,
    output logic [NC-1:0]               dbg_bridge_out_valid
);

    // Validate NUM_CHANNELS at elaboration time
    initial begin
        if (NC > 128) begin
            $fatal(1, "snk_sram_controller: NUM_CHANNELS=%0d exceeds maximum of 128", NC);
        end
    end

    //=========================================================================
    // ID-to-Channel Decode Logic
    //=========================================================================

    logic [NC-1:0] fill_valid_decoded;
    logic [NC-1:0] fill_ready_per_channel;
    logic [NC-1:0] drain_read_decoded;
    logic [NC-1:0][DW-1:0] drain_data_per_channel;
    logic [NC-1:0] fill_alloc_req_decoded;

    // Fill valid decode: fill_id selects which channel
    always_comb begin
        fill_valid_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (fill_valid && fill_id < NC) begin
            fill_valid_decoded[fill_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Fill ready mux: select ready from channel indicated by fill_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (fill_id < NC) begin
            fill_ready = fill_ready_per_channel[fill_id];
        end else begin
            fill_ready = 1'b0;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Drain read decode: drain_id selects which channel to drain
    always_comb begin
        drain_read_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (drain_read && drain_id < NC) begin
            drain_read_decoded[drain_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Drain data mux: select data from channel indicated by drain_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (drain_id < NC) begin
            drain_data = drain_data_per_channel[drain_id];
        end else begin
            drain_data = '0;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Fill allocation decode: fill_alloc_id selects which channel
    always_comb begin
        fill_alloc_req_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (fill_alloc_req && fill_alloc_id < NC) begin
            fill_alloc_req_decoded[fill_alloc_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    //=========================================================================
    // Per-Channel Unit Instantiation
    //=========================================================================

    generate
        for (genvar i = 0; i < NC; i++) begin : gen_snk_channel_units
            snk_sram_controller_unit_beats #(
                .DATA_WIDTH(DW),
                .SRAM_DEPTH(SD),
                .SEG_COUNT_WIDTH(SCW)
            ) u_snk_channel_unit (
                .clk                (clk),
                .rst_n              (rst_n),

                // Fill interface (Network Slave -> FIFO)
                .fill_valid         (fill_valid_decoded[i]),
                .fill_ready         (fill_ready_per_channel[i]),
                .fill_data          (fill_data),

                // Drain interface (FIFO -> AXI Write Engine)
                .drain_valid        (drain_valid[i]),
                .drain_ready        (drain_read_decoded[i]),
                .drain_data         (drain_data_per_channel[i]),

                // Fill allocation interface
                .fill_alloc_req     (fill_alloc_req_decoded[i]),
                .fill_alloc_size    (fill_alloc_size),
                .fill_space_free    (fill_space_free[i]),

                // Drain flow control interface
                .drain_req          (drain_req[i]),
                .drain_size         (drain_size[i]),
                .drain_data_avail   (drain_data_avail[i]),

                // Debug
                .dbg_bridge_pending   (dbg_bridge_pending[i]),
                .dbg_bridge_out_valid (dbg_bridge_out_valid[i])
            );
        end
    endgenerate

endmodule : snk_sram_controller_beats
