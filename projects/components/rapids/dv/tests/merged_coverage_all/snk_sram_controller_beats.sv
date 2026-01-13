//      // verilator_coverage annotation
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
 000591     input  logic                        clk,
%000003     input  logic                        rst_n,
        
            //=========================================================================
            // Fill Allocation Interface (Network Slave -> SRAM)
            // Single request with ID - ID selects which channel's space to check
            //=========================================================================
%000006     input  logic                        fill_alloc_req,
%000000     input  logic [7:0]                  fill_alloc_size,
%000000     input  logic [CIW-1:0]              fill_alloc_id,
%000000     output logic [NC-1:0][SCW-1:0]      fill_space_free,
        
            //=========================================================================
            // Fill Data Interface (Network Slave -> FIFO)
            // Transaction ID-based: single valid + ID selects channel
            //=========================================================================
 000060     input  logic                        fill_valid,
%000003     output logic                        fill_ready,
%000000     input  logic [CIW-1:0]              fill_id,
%000000     input  logic [DW-1:0]               fill_data,
        
            //=========================================================================
            // Drain Flow Control Interface (AXI Write Engine)
            //=========================================================================
%000000     output logic [NC-1:0][SCW-1:0]      drain_data_avail,
%000000     input  logic [NC-1:0]               drain_req,
%000000     input  logic [NC-1:0][7:0]          drain_size,
        
            //=========================================================================
            // Drain Data Interface (FIFO -> AXI Write Engine)
            //=========================================================================
%000004     output logic [NC-1:0]               drain_valid,
 000060     input  logic                        drain_read,
%000000     input  logic [CIW-1:0]              drain_id,
%000000     output logic [DW-1:0]               drain_data,
        
            //=========================================================================
            // Debug Interface
            //=========================================================================
%000000     output logic [NC-1:0]               dbg_bridge_pending,
%000004     output logic [NC-1:0]               dbg_bridge_out_valid
        );
        
            // Validate NUM_CHANNELS at elaboration time
%000003     initial begin
%000003         if (NC > 128) begin
                    $fatal(1, "snk_sram_controller: NUM_CHANNELS=%0d exceeds maximum of 128", NC);
                end
            end
        
            //=========================================================================
            // ID-to-Channel Decode Logic
            //=========================================================================
        
%000000     logic [NC-1:0] fill_valid_decoded;
%000002     logic [NC-1:0] fill_ready_per_channel;
%000000     logic [NC-1:0] drain_read_decoded;
            logic [NC-1:0][DW-1:0] drain_data_per_channel;
%000000     logic [NC-1:0] fill_alloc_req_decoded;
        
            // Fill valid decode: fill_id selects which channel
 001620     always_comb begin
 001620         fill_valid_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 000180         if (fill_valid && fill_id < NC) begin
 000180             fill_valid_decoded[fill_id] = 1'b1;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Fill ready mux: select ready from channel indicated by fill_id
%000003     always_comb begin
                /* verilator lint_off WIDTHEXPAND */
%000000         if (fill_id < NC) begin
%000003             fill_ready = fill_ready_per_channel[fill_id];
%000000         end else begin
%000000             fill_ready = 1'b0;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Drain read decode: drain_id selects which channel to drain
 001620     always_comb begin
 001620         drain_read_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 000180         if (drain_read && drain_id < NC) begin
 000180             drain_read_decoded[drain_id] = 1'b1;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Drain data mux: select data from channel indicated by drain_id
%000003     always_comb begin
                /* verilator lint_off WIDTHEXPAND */
%000000         if (drain_id < NC) begin
%000003             drain_data = drain_data_per_channel[drain_id];
%000000         end else begin
%000000             drain_data = '0;
                end
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Fill allocation decode: fill_alloc_id selects which channel
 001620     always_comb begin
 001620         fill_alloc_req_decoded = '0;
                /* verilator lint_off WIDTHEXPAND */
 000018         if (fill_alloc_req && fill_alloc_id < NC) begin
 000018             fill_alloc_req_decoded[fill_alloc_id] = 1'b1;
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
        
