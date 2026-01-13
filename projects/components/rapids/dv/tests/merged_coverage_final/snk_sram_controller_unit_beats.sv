//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: snk_sram_controller_unit
        // Purpose: Single-channel Sink SRAM Controller Unit
        //
        // Description:
        //   Single-channel SRAM controller unit for the SINK path containing:
        //   - Allocation controller (stream_alloc_ctrl)
        //   - FIFO buffer (gaxi_fifo_sync)
        //   - Latency bridge (stream_latency_bridge)
        //
        //   Data flow: Network Slave (fill) -> FIFO -> AXI Write Engine (drain)
        //
        //   This unit handles one channel's data flow from network ingress through
        //   buffering to AXI write with proper flow control.
        //
        // Parameters:
        //   - DATA_WIDTH: Data width in bits (default: 512)
        //   - SRAM_DEPTH: FIFO depth in entries (default: 512)
        //   - SEG_COUNT_WIDTH: Width for count signals
        //
        // Interfaces:
        //   - Fill side: Network Slave -> FIFO (valid/ready/data)
        //   - Drain side: FIFO -> Latency Bridge -> AXI Write Engine (valid/ready/data)
        //   - Allocation: Flow control for producer/consumer
        //
        // Based on: unified_sram_controller_unit.sv
        // Subsystem: rapids_macro_beats
        //
        // Author: RTL Design Sherpa
        // Created: 2026-01-10
        
        `timescale 1ns / 1ps
        
        `include "fifo_defs.svh"
        `include "reset_defs.svh"
        
        module snk_sram_controller_unit_beats #(
            // Primary parameters
            parameter int DATA_WIDTH = 512,
            parameter int SRAM_DEPTH = 512,
            parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
        
            // Short aliases
            parameter int DW = DATA_WIDTH,
            parameter int SD = SRAM_DEPTH,
            parameter int SCW = SEG_COUNT_WIDTH
        ) (
 020340     input  logic          clk,
 000060     input  logic          rst_n,
        
            //=========================================================================
            // Fill Allocation Interface (Network Slave -> SRAM)
            //=========================================================================
 000052     input  logic                  fill_alloc_req,
%000000     input  logic [7:0]            fill_alloc_size,
 000052     output logic [SCW-1:0]        fill_space_free,
        
            //=========================================================================
            // Fill Data Interface (Network Slave -> FIFO)
            //=========================================================================
 000160     input  logic                  fill_valid,
 000060     output logic                  fill_ready,
%000000     input  logic [DW-1:0]         fill_data,
        
            //=========================================================================
            // Drain Flow Control Interface (AXI Write Engine)
            //=========================================================================
%000000     output logic [SCW-1:0]        drain_data_avail,
 000186     input  logic                  drain_req,
%000000     input  logic [7:0]            drain_size,
        
            //=========================================================================
            // Drain Data Interface (FIFO -> AXI Write Engine)
            //=========================================================================
 000172     output logic                  drain_valid,
 000240     input  logic                  drain_ready,
%000000     output logic [DW-1:0]         drain_data,
        
            //=========================================================================
            // Debug Interface
            //=========================================================================
 000160     output logic                  dbg_bridge_pending,
 000172     output logic                  dbg_bridge_out_valid
        );
        
            //==========================================================================
            // Local Parameters
            //==========================================================================
            localparam int ADDR_WIDTH = $clog2(SD);
        
            //==========================================================================
            // Internal Signals
            //==========================================================================
 000052     logic [ADDR_WIDTH:0] alloc_space_free;
%000000     logic [ADDR_WIDTH:0] drain_data_available;
        
            // FIFO -> Latency Bridge
 000220     logic                fifo_rd_valid_internal;
 000144     logic                fifo_rd_ready_internal;
%000000     logic [DW-1:0]       fifo_rd_data_internal;
        
            // FIFO status
%000000     logic [ADDR_WIDTH:0] fifo_count;
        
            // Latency bridge status
 000084     logic [2:0]          bridge_occupancy;
        
            //==========================================================================
            // Allocation Controller (Space tracking for Network Slave)
            //==========================================================================
            alloc_ctrl_beats #(
                .DEPTH(SD),
                .REGISTERED(1)
            ) u_alloc_ctrl (
                .axi_aclk           (clk),
                .axi_aresetn        (rst_n),
        
                // Allocation request from Network Slave
                .wr_valid           (fill_alloc_req),
                .wr_size            (fill_alloc_size),
                .wr_ready           (),
        
                // Release when data exits controller
                .rd_valid           (drain_valid && drain_ready),
                .rd_ready           (),
        
                // Space tracking
                .space_free         (alloc_space_free),
        
                // Unused status
                .wr_full            (),
                .wr_almost_full     (),
                .rd_empty           (),
                .rd_almost_empty    ()
            );
        
            //==========================================================================
            // Drain Controller (Data tracking for AXI Write Engine)
            //==========================================================================
            drain_ctrl_beats #(
                .DEPTH(SD),
                .REGISTERED(1)
            ) u_drain_ctrl (
                .axi_aclk           (clk),
                .axi_aresetn        (rst_n),
        
                // Data written to FIFO
                .wr_valid           (fill_valid && fill_ready),
                .wr_ready           (),
        
                // Drain request from AXI Write Engine
                .rd_valid           (drain_req),
                .rd_size            (drain_size),
                .rd_ready           (),
        
                // Data tracking
                .data_available     (drain_data_available),
        
                // Unused status
                .wr_full            (),
                .wr_almost_full     (),
                .rd_empty           (),
                .rd_almost_empty    ()
            );
        
            //==========================================================================
            // FIFO Buffer (Physical Data Storage)
            //==========================================================================
            gaxi_fifo_sync #(
                .MEM_STYLE(FIFO_AUTO),
                .REGISTERED(1),
                .DATA_WIDTH(DW),
                .DEPTH(SD)
            ) u_channel_fifo (
                .axi_aclk       (clk),
                .axi_aresetn    (rst_n),
        
                // Write port (from Network Slave)
                .wr_valid       (fill_valid),
                .wr_ready       (fill_ready),
                .wr_data        (fill_data),
        
                // Read port (to Latency Bridge)
                .rd_valid       (fifo_rd_valid_internal),
                .rd_ready       (fifo_rd_ready_internal),
                .rd_data        (fifo_rd_data_internal),
        
                // Status
                .count          (fifo_count)
            );
        
            //==========================================================================
            // Latency Bridge (Aligns FIFO read latency)
            //==========================================================================
            latency_bridge_beats #(
                .DATA_WIDTH(DW)
            ) u_latency_bridge (
                .clk            (clk),
                .rst_n          (rst_n),
        
                // Slave (from FIFO)
                .s_data         (fifo_rd_data_internal),
                .s_valid        (fifo_rd_valid_internal),
                .s_ready        (fifo_rd_ready_internal),
        
                // Master (to AXI Write Engine)
                .m_data         (drain_data),
                .m_valid        (drain_valid),
                .m_ready        (drain_ready),
        
                // Status
                .occupancy      (bridge_occupancy),
        
                // Debug
                .dbg_r_pending      (dbg_bridge_pending),
                .dbg_r_out_valid    (dbg_bridge_out_valid)
            );
        
            //==========================================================================
            // Space/Count Reporting
            //==========================================================================
        
            // Total data available = drain controller + latency bridge
            assign drain_data_avail = drain_data_available + SCW'(bridge_occupancy);
        
            // Register fill_space_free to break combinatorial paths
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    fill_space_free <= SCW'(SD);
                end else begin
                    fill_space_free <= alloc_space_free;
                end
 000960     )
        
        endmodule : snk_sram_controller_unit_beats
        
