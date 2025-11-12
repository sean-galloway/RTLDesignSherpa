// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: datapath_wr_test
// Purpose: Write Data Path Test with 8 Scheduler Instances
//
// Description:
//   Test wrapper with 8 scheduler instances for realistic testing.
//   Each channel has its own descriptor interface driven by testbench GAXI masters.
//
//   Data Flow:
//     TB fills SRAM → 8× Schedulers → AXI Write Engine → AXI Bus
//
//   Simplified from scheduler_group architecture:
//   - No descriptor_engine (descriptors fed directly from testbench)
//   - No descriptor AXI interface (simple valid/ready/packet)
//   - Focus on scheduler → write engine → AXI data flow
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-11-05

`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module datapath_wr_test #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 4096,
    parameter int PIPELINE = 0,
    parameter int AW_MAX_OUTSTANDING = 8,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = ID_WIDTH,
    parameter int CW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SEG_SIZE = SRAM_DEPTH / NUM_CHANNELS,
    parameter int FD = SEG_SIZE,
    parameter int SEG_COUNT_WIDTH = $clog2(SEG_SIZE) + 1,

    // Descriptor width - 256 bits (STREAM descriptor format)
    parameter int DESC_WIDTH = 256
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,

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
    // Data AXI4 Master Interface (Shared by all channels)
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
    output logic [DW/8-1:0]             m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // B Channel
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    //=========================================================================
    // SRAM Write Interface (for TB to fill with test data)
    //=========================================================================
    input  logic                                axi_rd_sram_valid,   // TB drives valid (data to write)
    output logic                                axi_rd_sram_ready,   // Module ready
    input  logic [IW-1:0]                       axi_rd_sram_id,      // TB selects channel
    input  logic [DW-1:0]                       axi_rd_sram_data,    // Data from TB
    output logic [NC-1:0][SEG_COUNT_WIDTH-1:0]  axi_rd_space_free,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    // Bridge debug (for catching stuck occupancy bug)
    output logic [NC-1:0]               dbg_bridge_pending,
    output logic [NC-1:0]               dbg_bridge_out_valid,

    // Write engine debug (for monitoring write completion)
    output logic [31:0]                 dbg_aw_transactions,    // AW transaction count
    output logic [31:0]                 dbg_w_beats             // W beat count
);

    //=========================================================================
    // Internal Signal Arrays for Generate Loop
    //=========================================================================

    // Descriptor interface signals - always 8 channels (port interface is fixed)
    // Even if NUM_CHANNELS < 8, we need all 8 ports to be connectable
    logic [7:0]                  desc_valid;
    logic [7:0]                  desc_ready;
    logic [7:0][DESC_WIDTH-1:0]  desc_packet;
    logic [7:0]                  desc_error;

    // Scheduler → Read Engine interface (for write-only test, capture and auto-complete)
    logic [NC-1:0]                  sched_rd_valid;
    logic [NC-1:0][31:0]            sched_rd_beats;

    // Read completion generation (1-cycle delay to simulate read engine)
    logic [NC-1:0]                  r_rd_done_strobe;
    logic [NC-1:0][31:0]            r_rd_beats_done;

    // Scheduler → Write Engine interface
    logic [NC-1:0]                  sched_wr_valid;
    logic [NC-1:0]                  sched_wr_ready;
    logic [NC-1:0][AW-1:0]          sched_wr_addr;
    logic [NC-1:0][31:0]            sched_wr_beats;
    logic [NC-1:0][3:0]             sched_wr_channel_id;

    // Scheduler status
    logic [NC-1:0]                  sched_idle;
    logic [NC-1:0][6:0]             sched_state;  // One-hot encoded (7 states)

    // Scheduler completion strobes (from write engine)
    logic [NC-1:0]                  sched_wr_done_strobe;
    logic [NC-1:0][31:0]            sched_wr_beats_done;
    logic [NC-1:0]                  axi_wr_all_complete;

    // SRAM controller ↔ Write engine (direct connection - ID-based interface)
    logic [NC-1:0]                      axi_wr_sram_valid;           // Per-channel valid from SRAM
    logic                               axi_wr_sram_drain;           // Drain signal from write engine
    logic [CW-1:0]                      axi_wr_sram_id;              // Channel ID from write engine
    logic [DW-1:0]                      axi_wr_sram_data;            // Muxed data from SRAM

    // Write engine drain interface
    logic [NC-1:0]                      wr_drain_req;
    logic [NC-1:0][7:0]                 wr_drain_size;

    // Status
    logic [NC-1:0][SEG_COUNT_WIDTH-1:0] wr_drain_data_avail;

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
    // For write-only test: capture read request and complete in next cycle

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
                    r_rd_done_strobe[i] <= 1'b1;           // Assert strobe next cycle
                    r_rd_beats_done[i] <= sched_rd_beats[i]; // Complete all beats
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
            scheduler #(
                .CHANNEL_ID(i),
                .NUM_CHANNELS(NC),
                .ADDR_WIDTH(AW),
                .DATA_WIDTH(DW),
                .TIMEOUT_CYCLES(1000),
                .MON_AGENT_ID(8'h40),       // STREAM Scheduler
                .MON_UNIT_ID(4'h1),
                .MON_CHANNEL_ID(i)
            ) u_scheduler (
                .clk                    (clk),
                .rst_n                  (rst_n),

                // Configuration (tied off for test - channel always enabled)
                .cfg_channel_enable     (1'b1),
                .cfg_channel_reset      (1'b0),

                // Status
                .scheduler_idle         (sched_idle[i]),
                .scheduler_state        (sched_state[i]),

                // Descriptor interface (from testbench GAXI masters)
                .descriptor_valid       (desc_valid[i]),
                .descriptor_ready       (desc_ready[i]),
                .descriptor_packet      (desc_packet[i]),
                .descriptor_error       (desc_error[i]),

                // Data read interface (tied off for write-only test)
                .datard_valid           (sched_rd_valid[i]),
                .datard_ready           (1'b1),                    // Always ready
                .datard_addr            (),                        // Unused
                .datard_beats_remaining (sched_rd_beats[i]),
                .datard_channel_id      (),                        // Unused

                // Data write interface (to AXI write engine via arbiter)
                .datawr_valid           (sched_wr_valid[i]),
                .datawr_ready           (sched_wr_ready[i]),
                .datawr_addr            (sched_wr_addr[i]),
                .datawr_beats_remaining (sched_wr_beats[i]),
                .datawr_channel_id      (sched_wr_channel_id[i]),

                // Completion strobes from engines
                .datard_done_strobe     (r_rd_done_strobe[i]),     // Registered: asserts next cycle
                .datard_beats_done      (r_rd_beats_done[i]),      // All beats completed in 1 cycle
                .datawr_done_strobe     (sched_wr_done_strobe[i]),
                .datawr_beats_done      (sched_wr_beats_done[i]),

                // Error signals from engines
                .datard_error           (1'b0),
                .datawr_error           (1'b0),

                // Monitor bus (tied off for test)
                .mon_valid              (),
                .mon_ready              (1'b1),
                .mon_packet             ()
            );
        end
    endgenerate

    //=========================================================================
    // AXI Write Engine
    //=========================================================================

    axi_write_engine #(
        .NUM_CHANNELS(NC),
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .ID_WIDTH(IW),
        .SEG_COUNT_WIDTH(SEG_COUNT_WIDTH),
        .PIPELINE(PIPELINE),            // Pass through wrapper's PIPELINE parameter
        .AW_MAX_OUTSTANDING(AW_MAX_OUTSTANDING)  // Maximum outstanding AW requests per channel
    ) u_axi_write_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats  (cfg_axi_wr_xfer_beats),

        // Scheduler interface (8 channels)
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),
        .sched_wr_burst_len     ({NC{8'h0}}),  // Unused - engine decides burst len

        // Completion interface (to schedulers)
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),
        .axi_wr_all_complete    (axi_wr_all_complete),

        // Drain interface (to SRAM controller)
        .wr_drain_req           (wr_drain_req),
        .wr_drain_size          (wr_drain_size),
        .wr_drain_data_avail    (wr_drain_data_avail),

        // SRAM read interface (ID-based - direct connection)
        .axi_wr_sram_valid      (axi_wr_sram_valid),
        .axi_wr_sram_drain      (axi_wr_sram_drain),
        .axi_wr_sram_id         (axi_wr_sram_id),
        .axi_wr_sram_data       (axi_wr_sram_data),

        // AXI4 Master interface
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

        // Debug interface
        .dbg_aw_transactions    (dbg_aw_transactions),
        .dbg_w_beats            (dbg_w_beats)
    );

    //=========================================================================
    // SRAM Controller
    //=========================================================================

    sram_controller #(
        .NUM_CHANNELS(NC),
        .DATA_WIDTH(DW),
        .SRAM_DEPTH(SRAM_DEPTH / NC)  // sram_controller uses per-channel FIFOs
    ) u_sram_controller (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Allocation interface (unused - write engine doesn't use allocation)
        .axi_rd_alloc_req       (1'b0),
        .axi_rd_alloc_size      (8'h0),
        .axi_rd_alloc_id        (1'b0),                    // Tie to 0 (single channel ID)
        .axi_rd_space_free      (axi_rd_space_free),

        // Write interface (from testbench for filling SRAM)
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_id         (axi_rd_sram_id[CW-1:0]),  // Truncate top-level IW to CW
        .axi_rd_sram_data       (axi_rd_sram_data),

        // Drain interface (Write Engine Flow Control)
        .axi_wr_drain_req       (wr_drain_req),
        .axi_wr_drain_size      (wr_drain_size),
        .axi_wr_drain_data_avail(wr_drain_data_avail),

        // Read interface (to write engine - direct connection)
        .axi_wr_sram_valid      (axi_wr_sram_valid),         // Per-channel valids
        .axi_wr_sram_drain      (axi_wr_sram_drain),         // Single drain signal
        .axi_wr_sram_id         (axi_wr_sram_id),            // Channel ID select
        .axi_wr_sram_data       (axi_wr_sram_data),          // Muxed data output

        // Debug
        .dbg_bridge_pending     (dbg_bridge_pending),
        .dbg_bridge_out_valid   (dbg_bridge_out_valid)
    );

endmodule : datapath_wr_test
