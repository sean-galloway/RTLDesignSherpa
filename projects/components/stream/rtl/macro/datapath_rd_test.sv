// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: datapath_rd_test
// Purpose: Read Data Path Test with 8 Scheduler Instances
//
// Description:
//   Test wrapper with 8 scheduler instances for realistic testing.
//   Each channel has its own descriptor interface driven by testbench GAXI masters.
//
//   Data Flow:
//     8× Descriptor Packets → 8× Schedulers → AXI Read Engine → SRAM Controller
//
//   Simplified from scheduler_group architecture:
//   - No descriptor_engine (descriptors fed directly from testbench)
//   - No descriptor AXI interface (simple valid/ready/packet)
//   - Focus on scheduler → read engine → SRAM data flow
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-11-01

`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module datapath_rd_test #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8,
    parameter int MAX_BURST_LEN = 16,
    parameter int SRAM_DEPTH = 4096,
    parameter int PIPELINE = 0,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = ID_WIDTH,
    parameter int CW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SEG_SIZE = SRAM_DEPTH / NUM_CHANNELS,
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
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,

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
    // SRAM Read Interface (for TB to drain and verify)
    //=========================================================================
    output logic [NC-1:0]                       axi_wr_sram_valid,   // Per-channel valid (data available)
    input  logic                                axi_wr_sram_drain,   // TB drives ready (drain request)
    input  logic [IW-1:0]                       axi_wr_sram_id,      // TB selects channel
    output logic [DW-1:0]                       axi_wr_sram_data,    // Data from selected channel
    output logic [NC-1:0][SEG_COUNT_WIDTH-1:0]  axi_wr_data_available,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [31:0]                 dbg_r_beats_rcvd,
    output logic [31:0]                 dbg_sram_writes,

    // Bridge debug (for catching stuck occupancy bug)
    output logic [NC-1:0]               dbg_bridge_pending,
    output logic [NC-1:0]               dbg_bridge_out_valid,

    // Arbiter request debug (for bubble filtering)
    output logic [NC-1:0]               dbg_arb_request
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

    // Scheduler → Read Engine interface
    logic [NC-1:0]                  sched_rd_valid;
    logic [NC-1:0]                  sched_rd_ready;
    logic [NC-1:0][AW-1:0]          sched_rd_addr;
    logic [NC-1:0][31:0]            sched_rd_beats;
    logic [NC-1:0][3:0]             sched_rd_channel_id;

    // Scheduler → Write Engine interface (for read-only test, capture and auto-complete)
    logic [NC-1:0]                  sched_wr_valid;
    logic [NC-1:0][31:0]            sched_wr_beats;

    // Write completion generation (1-cycle delay to simulate write engine)
    logic [NC-1:0]                  r_wr_done_strobe;
    logic [NC-1:0][31:0]            r_wr_beats_done;

    // Scheduler status
    logic [NC-1:0]                  sched_idle;
    logic [NC-1:0][3:0]             sched_state;

    // Scheduler completion strobes (from read engine)
    logic [NC-1:0]                  sched_rd_done_strobe;
    logic [NC-1:0][31:0]            sched_rd_beats_done;

    // Read engine → SRAM controller
    logic           axi_rd_sram_valid;
    logic           axi_rd_sram_ready;
    logic [IW-1:0]  axi_rd_sram_id;
    logic [CW-1:0]  axi_rd_sram_channel_id;
    logic [DW-1:0]  axi_rd_sram_data;

    // Allocation interface
    logic           rd_alloc_req;
    logic [7:0]     rd_alloc_size;
    logic [IW-1:0]  rd_alloc_id;
    logic [CW-1:0]  rd_alloc_channel_id;
    logic [NC-1:0][SEG_COUNT_WIDTH-1:0] rd_space_free;

    // SRAM controller interface
    logic [CW-1:0] sram_wr_drain_channel_id;

    // Extract channel ID from full AXI ID
    assign axi_rd_sram_channel_id = axi_rd_sram_id[CW-1:0];
    assign rd_alloc_channel_id = rd_alloc_id[CW-1:0];
    assign sram_wr_drain_channel_id = axi_wr_sram_id[CW-1:0];

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
    // For read-only test: capture write request and complete in next cycle

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
                    r_wr_done_strobe[i] <= 1'b1;           // Assert strobe next cycle
                    r_wr_beats_done[i] <= sched_wr_beats[i]; // Complete all beats
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

                // Data read interface (to AXI read engine via arbiter)
                .datard_valid           (sched_rd_valid[i]),
                .datard_ready           (sched_rd_ready[i]),
                .datard_addr            (sched_rd_addr[i]),
                .datard_beats_remaining (sched_rd_beats[i]),
                .datard_channel_id      (sched_rd_channel_id[i]),

                // Data write interface (tied off for read-only test)
                .datawr_valid           (sched_wr_valid[i]),
                .datawr_ready           (1'b1),                    // Always ready
                .datawr_addr            (),                        // Unused
                .datawr_beats_remaining (sched_wr_beats[i]),
                .datawr_channel_id      (),                        // Unused

                // Completion strobes from engines
                .datard_done_strobe     (sched_rd_done_strobe[i]),
                .datard_beats_done      (sched_rd_beats_done[i]),
                .datawr_done_strobe     (r_wr_done_strobe[i]),     // Registered: asserts next cycle
                .datawr_beats_done      (r_wr_beats_done[i]),      // All beats completed in 1 cycle

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
    // AXI Read Engine
    //=========================================================================

    axi_read_engine #(
        .NUM_CHANNELS(NC),
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .ID_WIDTH(IW),
        .MAX_BURST_LEN(MAX_BURST_LEN),
        .COUNT_WIDTH(SEG_COUNT_WIDTH),
        .PIPELINE(PIPELINE)
    ) u_axi_read_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats  (cfg_axi_rd_xfer_beats),

        // Scheduler interface (8 channels)
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_ready         (sched_rd_ready),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),
        .sched_rd_burst_len     ({NC{8'h0}}),  // Unused - engine decides burst len

        // Completion interface (to schedulers)
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),

        // SRAM allocation interface
        .rd_alloc_req           (rd_alloc_req),
        .rd_alloc_size          (rd_alloc_size),
        .rd_alloc_id            (rd_alloc_id),
        .rd_space_free          (rd_space_free),

        // SRAM write interface
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_id         (axi_rd_sram_id),
        .axi_rd_sram_data       (axi_rd_sram_data),

        // AXI4 Master interface
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

        // Debug
        .dbg_r_beats_rcvd       (dbg_r_beats_rcvd),
        .dbg_sram_writes        (dbg_sram_writes),
        .dbg_arb_request        (dbg_arb_request)
    );

    //=========================================================================
    // SRAM Controller
    //=========================================================================

    sram_controller #(
        .NUM_CHANNELS(NC),
        .DATA_WIDTH(DW),
        .FIFO_DEPTH(SRAM_DEPTH / NC)  // sram_controller uses per-channel FIFOs
    ) u_sram_controller (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Allocation interface (from read engine)
        .axi_rd_alloc_req       (rd_alloc_req),
        .axi_rd_alloc_size      (rd_alloc_size),
        .axi_rd_alloc_id        (rd_alloc_channel_id),  // Channel ID only
        .axi_rd_space_free      (rd_space_free),

        // Write interface (from read engine)
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_id         (axi_rd_sram_channel_id),  // Channel ID only
        .axi_rd_sram_data       (axi_rd_sram_data),

        // Read interface (to testbench for verification)
        .axi_wr_sram_valid      (axi_wr_sram_valid),         // Per-channel valid
        .axi_wr_sram_drain      (axi_wr_sram_drain),
        .axi_wr_sram_id         (sram_wr_drain_channel_id),  // Channel ID only
        .axi_wr_sram_data       (axi_wr_sram_data),

        // Status
        .axi_wr_data_available  (axi_wr_data_available),

        // Debug
        .dbg_bridge_pending     (dbg_bridge_pending),
        .dbg_bridge_out_valid   (dbg_bridge_out_valid)
    );

endmodule : datapath_rd_test
