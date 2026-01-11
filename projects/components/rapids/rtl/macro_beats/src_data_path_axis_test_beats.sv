// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: source_data_path_axis_test
// Purpose: RAPIDS Beats Source Data Path Test with 8 Scheduler Instances
//
// Description:
//   Test wrapper with 8 scheduler instances for realistic testing.
//   Each channel has its own descriptor interface driven by testbench GAXI masters.
//
//   Data Flow:
//     8x Descriptor Packets -> 8x Schedulers -> AXI Read -> Source Data Path -> AXIS Master
//
//   Simplified from scheduler_group architecture:
//   - No descriptor_engine (descriptors fed directly from testbench)
//   - No descriptor AXI interface (simple valid/ready/packet)
//   - Focus on scheduler -> source data path -> AXIS master data flow
//
//   For read-only test (source path), write engine completion is auto-generated:
//   - When scheduler asserts sched_wr_valid, we immediately complete it
//   - This simulates "destination ready to receive data" scenario
//
// Subsystem: rapids_macro_beats
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module src_data_path_axis_test_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 4096,
    parameter int PIPELINE = 0,
    parameter int AR_MAX_OUTSTANDING = 8,

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
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,
    input  logic [7:0]                  cfg_drain_size,

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
    // AXI-Stream Master Interface (Network Output)
    //=========================================================================
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,

    //=========================================================================
    // AXI4 Read Master Interface (from Memory)
    //=========================================================================
    // AR Channel
    output logic [IW-1:0]               m_axi_arid,
    output logic [AW-1:0]               m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // R Channel
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [DW-1:0]               m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_rd_all_complete,
    output logic [31:0]                 dbg_r_beats_rcvd,
    output logic [31:0]                 dbg_sram_writes,
    output logic [NC-1:0]               dbg_arb_request,
    output logic [NC-1:0]               dbg_sram_bridge_pending,
    output logic [NC-1:0]               dbg_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_sent,
    output logic [31:0]                 dbg_axis_packets_sent,

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

    // Scheduler -> Read Engine interface
    logic [NC-1:0]                  sched_rd_valid;
    logic [NC-1:0][AW-1:0]          sched_rd_addr;
    logic [NC-1:0][31:0]            sched_rd_beats;

    // Scheduler -> Write Engine interface (for read-only test, auto-complete)
    logic [NC-1:0]                  sched_wr_valid;
    logic [NC-1:0]                  sched_wr_ready_internal;
    logic [NC-1:0][AW-1:0]          sched_wr_addr;
    logic [NC-1:0][31:0]            sched_wr_beats;

    // Write completion generation (auto-complete since this is read-only test)
    logic [NC-1:0]                  r_wr_done_strobe;
    logic [NC-1:0][31:0]            r_wr_beats_done;

    // Scheduler completion strobes (from read engine)
    logic [NC-1:0]                  sched_rd_done_strobe;
    logic [NC-1:0][31:0]            sched_rd_beats_done;
    logic [NC-1:0]                  sched_rd_error;

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
    // Write Completion Logic (Read-Only Test)
    //=========================================================================
    // For read-only test: auto-complete write requests immediately
    // This simulates "AXIS destination always ready" scenario

    // Always ready for write requests
    assign sched_wr_ready_internal = '{default:1'b1};

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_done_strobe <= '{default:0};
            r_wr_beats_done <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Default: clear strobe after 1 cycle
                r_wr_done_strobe[i] <= 1'b0;

                // When scheduler asserts write request, complete it next cycle
                if (sched_wr_valid[i]) begin
                    r_wr_done_strobe[i] <= 1'b1;
                    r_wr_beats_done[i] <= sched_wr_beats[i];
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

                // Data read interface (to source data path)
                .sched_rd_valid         (sched_rd_valid[i]),
                .sched_rd_addr          (sched_rd_addr[i]),
                .sched_rd_beats         (sched_rd_beats[i]),

                // Data write interface (auto-completed for read-only test)
                .sched_wr_valid         (sched_wr_valid[i]),
                .sched_wr_ready         (sched_wr_ready_internal[i]),
                .sched_wr_addr          (sched_wr_addr[i]),
                .sched_wr_beats         (sched_wr_beats[i]),

                // Completion strobes
                .sched_rd_done_strobe   (sched_rd_done_strobe[i]),
                .sched_rd_beats_done    (sched_rd_beats_done[i]),
                .sched_wr_done_strobe   (r_wr_done_strobe[i]),
                .sched_wr_beats_done    (r_wr_beats_done[i]),

                // Error signals
                .sched_rd_error         (sched_rd_error[i]),
                .sched_wr_error         (1'b0),

                // Monitor bus (tied off for test)
                .mon_valid              (),
                .mon_ready              (1'b1),
                .mon_packet             ()
            );
        end
    endgenerate

    //=========================================================================
    // Source Data Path with AXIS Instance
    //=========================================================================

    src_data_path_axis_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SRAM_DEPTH / NC),
        .SEG_COUNT_WIDTH    (SEG_COUNT_WIDTH),
        .PIPELINE           (PIPELINE),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .AXIS_ID_WIDTH      (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH    (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH    (AXIS_USER_WIDTH)
    ) u_source_data_path_axis (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats  (cfg_axi_rd_xfer_beats),
        .cfg_drain_size         (cfg_drain_size),

        // Scheduler Interface
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Completion Interface
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_rd_error         (sched_rd_error),

        // AXIS Master Interface
        .m_axis_tdata           (m_axis_tdata),
        .m_axis_tstrb           (m_axis_tstrb),
        .m_axis_tlast           (m_axis_tlast),
        .m_axis_tid             (m_axis_tid),
        .m_axis_tdest           (m_axis_tdest),
        .m_axis_tuser           (m_axis_tuser),
        .m_axis_tvalid          (m_axis_tvalid),
        .m_axis_tready          (m_axis_tready),

        // AXI Read Master Interface
        .m_axi_arid             (m_axi_arid),
        .m_axi_araddr           (m_axi_araddr),
        .m_axi_arlen            (m_axi_arlen),
        .m_axi_arsize           (m_axi_arsize),
        .m_axi_arburst          (m_axi_arburst),
        .m_axi_arvalid          (m_axi_arvalid),
        .m_axi_arready          (m_axi_arready),

        .m_axi_rid              (m_axi_rid),
        .m_axi_rdata            (m_axi_rdata),
        .m_axi_rresp            (m_axi_rresp),
        .m_axi_rlast            (m_axi_rlast),
        .m_axi_rvalid           (m_axi_rvalid),
        .m_axi_rready           (m_axi_rready),

        // Debug Interface
        .dbg_rd_all_complete    (dbg_rd_all_complete),
        .dbg_r_beats_rcvd       (dbg_r_beats_rcvd),
        .dbg_sram_writes        (dbg_sram_writes),
        .dbg_arb_request        (dbg_arb_request),
        .dbg_sram_bridge_pending    (dbg_sram_bridge_pending),
        .dbg_sram_bridge_out_valid  (dbg_sram_bridge_out_valid),
        .dbg_axis_beats_sent    (dbg_axis_beats_sent),
        .dbg_axis_packets_sent  (dbg_axis_packets_sent)
    );

endmodule : src_data_path_axis_test_beats
