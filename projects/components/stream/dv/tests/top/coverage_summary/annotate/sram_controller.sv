//      // verilator_coverage annotation
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
            // Primary parameters (long names for external configuration)
            parameter int NUM_CHANNELS = 8,
            parameter int DATA_WIDTH = 512,
            parameter int SRAM_DEPTH = 512,                  // Depth per channel SRAM
            parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,  // Width of count signals
        
            // Short aliases (for internal use)
            parameter int NC = NUM_CHANNELS,
            parameter int DW = DATA_WIDTH,
            parameter int SD = SRAM_DEPTH,
            parameter int SCW = SEG_COUNT_WIDTH,             // Segment count width
            parameter int CIW = (NC > 1) ? $clog2(NC) : 1    // Channel ID width (min 1 bit)
        ) (
 002323     input  logic                        clk,
%000001     input  logic                        rst_n,
        
            //=========================================================================
            // Allocation Interface (for AXI Read Engine flow control)
            // Single request with ID - ID selects which channel's space to check
            //=========================================================================
 000016     input  logic                        axi_rd_alloc_req,        // Allocation request
%000000     input  logic [7:0]                  axi_rd_alloc_size,       // Number of beats to allocate
%000000     input  logic [CIW-1:0]              axi_rd_alloc_id,         // Channel ID for allocation
%000000     output logic [NC-1:0][SCW-1:0]      axi_rd_alloc_space_free, // Free space in each FIFO
        
            //=========================================================================
            // Write Interface (AXI Read Engine → FIFO)
            // Transaction ID-based: single valid + ID selects channel
            //=========================================================================
%000004     input  logic                        axi_rd_sram_valid,      // Single valid
%000001     output logic                        axi_rd_sram_ready,      // Ready (muxed from selected channel)
%000000     input  logic [CIW-1:0]              axi_rd_sram_id,         // Channel ID select
            input  logic [DW-1:0]               axi_rd_sram_data,       // common data bus
        
            //=========================================================================
            // Drain Interface (Write Engine Flow Control)
            //=========================================================================
%000000     output logic [NC-1:0][SCW-1:0]      axi_wr_drain_data_avail,  // Available data after reservations
%000000     input  logic [NC-1:0]               axi_wr_drain_req,         // Per-channel drain request
%000000     input  logic [NC-1:0][7:0]          axi_wr_drain_size,        // Per-channel drain size
        
            //=========================================================================
            // Read Interface (FIFO → AXI Write Engine)
            //=========================================================================
%000002     output logic [NC-1:0]               axi_wr_sram_valid,      // Per-channel valid (data available)
 000188     input  logic                        axi_wr_sram_drain,      // Ready (consumer requests data)
%000000     input  logic [CIW-1:0]              axi_wr_sram_id,         // Channel ID select
            output logic [DW-1:0]               axi_wr_sram_data,       // Data from selected channel
        
            //=========================================================================
            // Debug Interface (for catching bridge bugs)
            //=========================================================================
%000000     output logic [NC-1:0]               dbg_bridge_pending,
%000002     output logic [NC-1:0]               dbg_bridge_out_valid
        );
        
            //=========================================================================
            // ID-to-Channel Decode Logic
            //=========================================================================
            // Decode transaction IDs to per-channel enables and mux ready signals
            //=========================================================================
        
%000000     logic [NC-1:0] axi_rd_sram_valid_decoded;
%000001     logic [NC-1:0] axi_rd_sram_ready_per_channel;
%000000     logic [NC-1:0] axi_wr_sram_drain_decoded;
            logic [NC-1:0][DW-1:0] axi_wr_sram_data_per_channel;
%000000     logic [NC-1:0] axi_rd_alloc_req_decoded;
        
            // Write valid decode: axi_rd_sram_id selects which channel
 010968     always_comb begin
 010968         axi_rd_sram_valid_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 001319         if (axi_rd_sram_valid && axi_rd_sram_id < NC) begin
 001319             axi_rd_sram_valid_decoded[axi_rd_sram_id] = 1'b1;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Ready mux: select ready from channel indicated by axi_rd_sram_id
%000001     always_comb begin
                /* verilator lint_off WIDTHEXPAND */
%000000         if (axi_rd_sram_id < NC) begin
%000001             axi_rd_sram_ready = axi_rd_sram_ready_per_channel[axi_rd_sram_id];
%000000         end else begin
%000000             axi_rd_sram_ready = 1'b0;  // Invalid ID → not ready
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Read/drain decode: axi_wr_sram_id selects which channel to drain
 010968     always_comb begin
 010968         axi_wr_sram_drain_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 001415         if (axi_wr_sram_drain && axi_wr_sram_id < NC) begin
 001415             axi_wr_sram_drain_decoded[axi_wr_sram_id] = 1'b1;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Data mux: select data from channel indicated by axi_wr_sram_id
%000001     always_comb begin
                /* verilator lint_off WIDTHEXPAND */
%000000         if (axi_wr_sram_id < NC) begin
%000001             axi_wr_sram_data = axi_wr_sram_data_per_channel[axi_wr_sram_id];
%000000         end else begin
%000000             axi_wr_sram_data = '0;  // Invalid ID → zero data
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Read allocation decode: axi_rd_alloc_id selects which channel
 010968     always_comb begin
 010968         axi_rd_alloc_req_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 000084         if (axi_rd_alloc_req && axi_rd_alloc_id < NC) begin
 000084             axi_rd_alloc_req_decoded[axi_rd_alloc_id] = 1'b1;
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
                        .SRAM_DEPTH(SRAM_DEPTH),
                        .SEG_COUNT_WIDTH(SEG_COUNT_WIDTH)
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
                        .axi_rd_alloc_req       (axi_rd_alloc_req_decoded[i]),
                        .axi_rd_alloc_size      (axi_rd_alloc_size),         // SHARED - all see same size
                        .axi_rd_alloc_space_free(axi_rd_alloc_space_free[i]),
        
                        // Drain interface (Write Engine Flow Control)
                        .axi_wr_drain_req       (axi_wr_drain_req[i]),
                        .axi_wr_drain_size      (axi_wr_drain_size[i]),
                        .axi_wr_drain_data_avail(axi_wr_drain_data_avail[i]),
        
                        // Debug
                        .dbg_bridge_pending     (dbg_bridge_pending[i]),
                        .dbg_bridge_out_valid   (dbg_bridge_out_valid[i])
                    );
                end
            endgenerate
        
        endmodule : sram_controller
        
