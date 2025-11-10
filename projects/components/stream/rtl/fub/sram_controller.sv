// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sram_controller
// Purpose: Simple SRAM Controller using per-channel FIFOs with Latency Bridge
//
// Description:
//   Replaces complex shared SRAM with segmentation logic with
//   simple per-channel gaxi_fifo_sync blocks.
//
// Architecture:
//   - Write Path: AXI Read Engine → Allocation Controller → FIFO
//   - Read Path: FIFO → Latency Bridge → AXI Write Engine
//   - Per-channel space tracking and data counting
//
// Key Features:
//   - Independent FIFO per channel (no segmentation complexity)
//   - Allocation controller tracks reserved vs. committed space
//   - Latency bridge aligns FIFO read latency (registered output)
//   - Saturating 8-bit space/count reporting
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_fub

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module sram_controller #(
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int FIFO_DEPTH = 512,  // Depth per channel
    parameter int NC = NUM_CHANNELS,
    parameter int DW = DATA_WIDTH,
    parameter int IW = (NC > 1) ? $clog2(NC) : 1    // ID width (min 1 bit)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    //=========================================================================
    // Write Interface (AXI Read Engine → FIFO)
    // Transaction ID-based: single valid + ID selects channel
    //=========================================================================
    input  logic                    axi_rd_sram_valid,      // Single valid
    input  logic [IW-1:0]           axi_rd_sram_id,         // Channel ID select
    output logic                    axi_rd_sram_ready,      // Ready (muxed from selected channel)
    input  logic [DW-1:0]           axi_rd_sram_data,       // common data bus

    //=========================================================================
    // Allocation Interface (for AXI Read Engine flow control)
    // Single request with ID - ID selects which channel's space to check
    //=========================================================================
    input  logic                                axi_rd_alloc_req,       // Allocation request
    input  logic [7:0]                          axi_rd_alloc_size,      // Number of beats to allocate
    input  logic [IW-1:0]                       axi_rd_alloc_id,        // Channel ID for allocation
    output logic [NC-1:0][$clog2(FIFO_DEPTH):0] axi_rd_space_free,      // Free space in each FIFO

    //=========================================================================
    // Read Interface (FIFO → AXI Write Engine)
    //=========================================================================
    output logic [NC-1:0][$clog2(FIFO_DEPTH):0] axi_wr_data_available,  // Data count in each FIFO
    output logic [NC-1:0]           axi_wr_sram_valid,      // Per-channel valid (data available)
    input  logic                    axi_wr_sram_drain,      // Ready (consumer requests data)
    input  logic [IW-1:0]           axi_wr_sram_id,         // Channel ID select
    output logic [DW-1:0]           axi_wr_sram_data,       // Data from selected channel

    //=========================================================================
    // Debug Interface (for catching bridge bugs)
    //=========================================================================
    output logic [NC-1:0]           dbg_bridge_pending,
    output logic [NC-1:0]           dbg_bridge_out_valid
);

    //=========================================================================
    // ID-to-Channel Decode Logic
    //=========================================================================
    // Decode transaction IDs to per-channel enables and mux ready signals
    //=========================================================================

    logic [NC-1:0] axi_rd_sram_valid_decoded;
    logic [NC-1:0] axi_rd_sram_ready_per_channel;
    logic [NC-1:0] axi_wr_sram_drain_decoded;
    logic [NC-1:0][DW-1:0] axi_wr_sram_data_per_channel;
    logic [NC-1:0] axi_rd_alloc_req_decoded;

    // Write valid decode: axi_rd_sram_id selects which channel
    always_comb begin
        axi_rd_sram_valid_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_sram_valid && axi_rd_sram_id < NC) begin
            axi_rd_sram_valid_decoded[axi_rd_sram_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Ready mux: select ready from channel indicated by axi_rd_sram_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_sram_id < NC) begin
            axi_rd_sram_ready = axi_rd_sram_ready_per_channel[axi_rd_sram_id];
        end else begin
            axi_rd_sram_ready = 1'b0;  // Invalid ID → not ready
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Read/drain decode: axi_wr_sram_id selects which channel to drain
    always_comb begin
        axi_wr_sram_drain_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_wr_sram_drain && axi_wr_sram_id < NC) begin
            axi_wr_sram_drain_decoded[axi_wr_sram_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Data mux: select data from channel indicated by axi_wr_sram_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (axi_wr_sram_id < NC) begin
            axi_wr_sram_data = axi_wr_sram_data_per_channel[axi_wr_sram_id];
        end else begin
            axi_wr_sram_data = '0;  // Invalid ID → zero data
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Read allocation decode: axi_rd_alloc_id selects which channel
    always_comb begin
        axi_rd_alloc_req_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_alloc_req && axi_rd_alloc_id < NC) begin
            axi_rd_alloc_req_decoded[axi_rd_alloc_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    //=========================================================================
    // Per-Channel Unit Instantiation
    //=========================================================================
    // Each channel has its own allocation controller, FIFO, and latency bridge
    // encapsulated in a single unit for cleaner hierarchy.
    //=========================================================================

    generate
        for (genvar i = 0; i < NC; i++) begin : gen_channel_units
            sram_controller_unit #(
                .DATA_WIDTH(DW),
                .FIFO_DEPTH(FIFO_DEPTH)
            ) u_channel_unit (
                .clk                (clk),
                .rst_n              (rst_n),

                // Write interface (AXI Read Engine → FIFO)
                // Decoded valid from ID - only selected channel sees valid
                .axi_rd_sram_valid  (axi_rd_sram_valid_decoded[i]),
                .axi_rd_sram_ready  (axi_rd_sram_ready_per_channel[i]),
                .axi_rd_sram_data   (axi_rd_sram_data),      // SHARED - all units see same data

                // Read interface (FIFO → Latency Bridge → AXI Write Engine)
                // Decoded drain connects to ready (consumer requests data)
                .axi_wr_sram_valid  (axi_wr_sram_valid[i]),  // Per-channel valid to top level
                .axi_wr_sram_ready  (axi_wr_sram_drain_decoded[i]),
                .axi_wr_sram_data   (axi_wr_sram_data_per_channel[i]),

                // Allocation interface (Read Engine Flow Control)
                // Decoded from ID - only selected channel sees req
                .rd_alloc_req       (axi_rd_alloc_req_decoded[i]),
                .rd_alloc_size      (axi_rd_alloc_size),         // SHARED - all see same size
                .rd_space_free      (axi_rd_space_free[i]),

                // Data available (for Write Engine visibility)
                .wr_data_available  (axi_wr_data_available[i]),

                // Debug
                .dbg_bridge_pending     (dbg_bridge_pending[i]),
                .dbg_bridge_out_valid   (dbg_bridge_out_valid[i])
            );
        end
    endgenerate

endmodule : sram_controller
