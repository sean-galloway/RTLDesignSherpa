// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sink_data_path_axis_test
// Purpose: RAPIDS Beats Sink Data Path Test with 8 Scheduler Instances
//
// Description:
//   Test wrapper with 8 scheduler instances for realistic testing.
//   Each channel has its own descriptor interface driven by testbench GAXI masters.
//
//   Data Flow:
//     8x Descriptor Packets -> 8x Schedulers -> AXIS Slave -> Sink Data Path -> AXI Write
//
//   Simplified from scheduler_group architecture:
//   - No descriptor_engine (descriptors fed directly from testbench)
//   - No descriptor AXI interface (simple valid/ready/packet)
//   - Focus on scheduler -> sink data path -> AXI write data flow
//
//   For write-only test (sink path), read engine completion is auto-generated:
//   - When scheduler asserts sched_rd_valid, we immediately complete it
//   - This simulates "source data already available in SRAM" scenario
//
// Subsystem: rapids_macro_beats
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module snk_data_path_axis_test_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 4096,
    parameter int PIPELINE = 0,
    parameter int AW_MAX_OUTSTANDING = 8,
    parameter int W_PHASE_FIFO_DEPTH = 64,
    parameter int B_PHASE_FIFO_DEPTH = 16,

    // AXIS parameters
    parameter int AXIS_ID_WIDTH = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int CW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SEG_SIZE = SRAM_DEPTH / NUM_CHANNELS,
    parameter int SEG_COUNT_WIDTH = $clog2(SEG_SIZE) + 1,
    parameter int SW = DW / 8,

    // Descriptor width - 256 bits (RAPIDS descriptor format)
    parameter int DESC_WIDTH = 256
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,
    input  logic [7:0]                  cfg_alloc_size,

    //=========================================================================
    // Descriptor Interfaces (8 channels) - Simple valid/ready/packet pattern
    // Pattern: descriptor_N_signal for easy GAXI master auto-connect
    //=========================================================================

    // Channel 0
    input  logic                        descriptor_0_valid,
    output logic                        descriptor_0_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_0_packet,
    input  logic                        descriptor_0_error,

    // Channel 1
    input  logic                        descriptor_1_valid,
    output logic                        descriptor_1_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_1_packet,
    input  logic                        descriptor_1_error,

    // Channel 2
    input  logic                        descriptor_2_valid,
    output logic                        descriptor_2_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_2_packet,
    input  logic                        descriptor_2_error,

    // Channel 3
    input  logic                        descriptor_3_valid,
    output logic                        descriptor_3_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_3_packet,
    input  logic                        descriptor_3_error,

    // Channel 4
    input  logic                        descriptor_4_valid,
    output logic                        descriptor_4_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_4_packet,
    input  logic                        descriptor_4_error,

    // Channel 5
    input  logic                        descriptor_5_valid,
    output logic                        descriptor_5_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_5_packet,
    input  logic                        descriptor_5_error,

    // Channel 6
    input  logic                        descriptor_6_valid,
    output logic                        descriptor_6_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_6_packet,
    input  logic                        descriptor_6_error,

    // Channel 7
    input  logic                        descriptor_7_valid,
    output logic                        descriptor_7_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_7_packet,
    input  logic                        descriptor_7_error,

    //=========================================================================
    // AXI-Stream Slave Interface (Network Input)
    //=========================================================================
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    //=========================================================================
    // AXI4 Write Master Interface (to Memory)
    //=========================================================================
    // AW Channel
    output logic [IW-1:0]               m_axi_awid,
    output logic [AW-1:0]               m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // W Channel
    output logic [DW-1:0]               m_axi_wdata,
    output logic [(DW/8)-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // B Channel
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_sram_bridge_pending,
    output logic [NC-1:0]               dbg_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_received,
    output logic [31:0]                 dbg_axis_packets_received,

    //=========================================================================
    // Status Interface (Scheduler state)
    //=========================================================================
    output logic [NC-1:0]               sched_idle,
    output logic [NC-1:0][6:0]          sched_state,
    output logic [NC-1:0]               sched_error
);

    //=========================================================================
    // Internal Signal Arrays for Generate Loop
    //=========================================================================

    // Descriptor interface signals - always 8 channels
    logic [7:0]                  desc_valid;
    logic [7:0]                  desc_ready;
    logic [7:0][DESC_WIDTH-1:0]  desc_packet;
    logic [7:0]                  desc_error;

    // Scheduler -> Write Engine interface
    logic [NC-1:0]                  sched_wr_valid;
    logic [NC-1:0]                  sched_wr_ready_internal;
    logic [NC-1:0][AW-1:0]          sched_wr_addr;
    logic [NC-1:0][31:0]            sched_wr_beats;

    // Scheduler -> Read Engine interface (for write-only test, auto-complete)
    logic [NC-1:0]                  sched_rd_valid;
    logic [NC-1:0][AW-1:0]          sched_rd_addr;
    logic [NC-1:0][31:0]            sched_rd_beats;

    // Read completion generation (auto-complete since this is write-only test)
    logic [NC-1:0]                  r_rd_done_strobe;
    logic [NC-1:0][31:0]            r_rd_beats_done;

    // Scheduler completion strobes (from write engine)
    logic [NC-1:0]                  sched_wr_done_strobe;
    logic [NC-1:0][31:0]            sched_wr_beats_done;

    //=========================================================================
    // Map Individual Port Signals to Internal Arrays
    //=========================================================================

    // Channel 0
    assign desc_valid[0] = descriptor_0_valid;
    assign descriptor_0_ready = desc_ready[0];
    assign desc_packet[0] = descriptor_0_packet;
    assign desc_error[0] = descriptor_0_error;

    // Channel 1
    assign desc_valid[1] = descriptor_1_valid;
    assign descriptor_1_ready = desc_ready[1];
    assign desc_packet[1] = descriptor_1_packet;
    assign desc_error[1] = descriptor_1_error;

    // Channel 2
    assign desc_valid[2] = descriptor_2_valid;
    assign descriptor_2_ready = desc_ready[2];
    assign desc_packet[2] = descriptor_2_packet;
    assign desc_error[2] = descriptor_2_error;

    // Channel 3
    assign desc_valid[3] = descriptor_3_valid;
    assign descriptor_3_ready = desc_ready[3];
    assign desc_packet[3] = descriptor_3_packet;
    assign desc_error[3] = descriptor_3_error;

    // Channel 4
    assign desc_valid[4] = descriptor_4_valid;
    assign descriptor_4_ready = desc_ready[4];
    assign desc_packet[4] = descriptor_4_packet;
    assign desc_error[4] = descriptor_4_error;

    // Channel 5
    assign desc_valid[5] = descriptor_5_valid;
    assign descriptor_5_ready = desc_ready[5];
    assign desc_packet[5] = descriptor_5_packet;
    assign desc_error[5] = descriptor_5_error;

    // Channel 6
    assign desc_valid[6] = descriptor_6_valid;
    assign descriptor_6_ready = desc_ready[6];
    assign desc_packet[6] = descriptor_6_packet;
    assign desc_error[6] = descriptor_6_error;

    // Channel 7
    assign desc_valid[7] = descriptor_7_valid;
    assign descriptor_7_ready = desc_ready[7];
    assign desc_packet[7] = descriptor_7_packet;
    assign desc_error[7] = descriptor_7_error;

    //=========================================================================
    // Read Completion Logic (Write-Only Test)
    //=========================================================================
    // For write-only test: auto-complete read requests immediately
    // This simulates "data already available from AXIS" scenario

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_done_strobe <= '{default:0};
            r_rd_beats_done <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Default: clear strobe after 1 cycle
                r_rd_done_strobe[i] <= 1'b0;

                // When scheduler asserts read request, complete it next cycle
                if (sched_rd_valid[i]) begin
                    r_rd_done_strobe[i] <= 1'b1;
                    r_rd_beats_done[i] <= sched_rd_beats[i];
                end
            end
        end
    )

    //=========================================================================
    // Scheduler Instances (8 channels)
    //=========================================================================

    genvar i;
    generate
        for (i = 0; i < NC; i++) begin : gen_schedulers
            scheduler_beats #(
                .CHANNEL_ID(i),
                .NUM_CHANNELS(NC),
                .ADDR_WIDTH(AW),
                .DATA_WIDTH(DW),
                .MON_AGENT_ID(8'h40),
                .MON_UNIT_ID(4'h1),
                .MON_CHANNEL_ID(i)
            ) u_scheduler (
                .clk                    (clk),
                .rst_n                  (rst_n),

                // Configuration (channel always enabled for test)
                .cfg_channel_enable     (1'b1),
                .cfg_channel_reset      (1'b0),
                .cfg_sched_timeout_cycles(16'd1000),
                .cfg_sched_timeout_enable(1'b1),

                // Status
                .scheduler_idle         (sched_idle[i]),
                .scheduler_state        (sched_state[i]),
                .sched_error            (sched_error[i]),

                // Descriptor interface (from testbench GAXI masters)
                .descriptor_valid       (desc_valid[i]),
                .descriptor_ready       (desc_ready[i]),
                .descriptor_packet      (desc_packet[i]),
                .descriptor_error       (desc_error[i]),

                // Data read interface (auto-completed for write-only test)
                .sched_rd_valid         (sched_rd_valid[i]),
                .sched_rd_addr          (sched_rd_addr[i]),
                .sched_rd_beats         (sched_rd_beats[i]),

                // Data write interface (to sink data path)
                .sched_wr_valid         (sched_wr_valid[i]),
                .sched_wr_ready         (sched_wr_ready_internal[i]),
                .sched_wr_addr          (sched_wr_addr[i]),
                .sched_wr_beats         (sched_wr_beats[i]),

                // Completion strobes
                .sched_rd_done_strobe   (r_rd_done_strobe[i]),
                .sched_rd_beats_done    (r_rd_beats_done[i]),
                .sched_wr_done_strobe   (sched_wr_done_strobe[i]),
                .sched_wr_beats_done    (sched_wr_beats_done[i]),

                // Error signals
                .sched_rd_error         (1'b0),
                .sched_wr_error         (1'b0),

                // Monitor bus (tied off for test)
                .mon_valid              (),
                .mon_ready              (1'b1),
                .mon_packet             ()
            );
        end
    endgenerate

    //=========================================================================
    // Sink Data Path with AXIS Instance
    //=========================================================================

    snk_data_path_axis_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SRAM_DEPTH / NC),
        .SEG_COUNT_WIDTH    (SEG_COUNT_WIDTH),
        .PIPELINE           (PIPELINE),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH (B_PHASE_FIFO_DEPTH),
        .AXIS_ID_WIDTH      (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH    (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH    (AXIS_USER_WIDTH)
    ) u_sink_data_path_axis (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats  (cfg_axi_wr_xfer_beats),
        .cfg_alloc_size         (cfg_alloc_size),

        // AXIS Slave Interface
        .s_axis_tdata           (s_axis_tdata),
        .s_axis_tstrb           (s_axis_tstrb),
        .s_axis_tlast           (s_axis_tlast),
        .s_axis_tid             (s_axis_tid),
        .s_axis_tdest           (s_axis_tdest),
        .s_axis_tuser           (s_axis_tuser),
        .s_axis_tvalid          (s_axis_tvalid),
        .s_axis_tready          (s_axis_tready),

        // Scheduler Interface
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready_internal),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),
        .sched_wr_burst_len     ('{default:cfg_axi_wr_xfer_beats}),

        // Completion Interface
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),

        // AXI Write Master Interface
        .m_axi_awid             (m_axi_awid),
        .m_axi_awaddr           (m_axi_awaddr),
        .m_axi_awlen            (m_axi_awlen),
        .m_axi_awsize           (m_axi_awsize),
        .m_axi_awburst          (m_axi_awburst),
        .m_axi_awvalid          (m_axi_awvalid),
        .m_axi_awready          (m_axi_awready),

        .m_axi_wdata            (m_axi_wdata),
        .m_axi_wstrb            (m_axi_wstrb),
        .m_axi_wlast            (m_axi_wlast),
        .m_axi_wvalid           (m_axi_wvalid),
        .m_axi_wready           (m_axi_wready),

        .m_axi_bid              (m_axi_bid),
        .m_axi_bresp            (m_axi_bresp),
        .m_axi_bvalid           (m_axi_bvalid),
        .m_axi_bready           (m_axi_bready),

        // Debug Interface
        .dbg_sram_bridge_pending    (dbg_sram_bridge_pending),
        .dbg_sram_bridge_out_valid  (dbg_sram_bridge_out_valid),
        .dbg_axis_beats_received    (dbg_axis_beats_received),
        .dbg_axis_packets_received  (dbg_axis_packets_received)
    );

endmodule : snk_data_path_axis_test_beats
