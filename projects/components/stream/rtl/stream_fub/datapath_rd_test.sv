// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: datapath_rd_test
// Purpose: Read Data Path Test Wrapper (AXI Read → SRAM Controller → SRAM)
//
// Description:
//   Integration test wrapper for validating the read data path streaming performance.
//   Tests data flow from AXI read transactions into SRAM buffer without stalls.
//
//   Data Flow:
//     AXI Master (Memory) → AXI Read Engine → SRAM Controller → SRAM Buffer
//
//   Key Validation Points:
//     - AXI AR/R channel streaming without backpressure
//     - SRAM Controller write path performance
//     - Buffer management and flow control
//     - No stalls under continuous streaming
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-10-26

`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module datapath_rd_test #(
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8,
    parameter int MAX_BURST_LEN = 16,
    parameter int SRAM_DEPTH = 4096,
    parameter int SRAM_ADDR_WIDTH = $clog2(SRAM_DEPTH),
    parameter int SEG_SIZE = SRAM_DEPTH / NUM_CHANNELS,
    parameter int SEG_PTR_WIDTH = $clog2(SEG_SIZE),
    parameter int SEG_COUNT_WIDTH = $clog2(SEG_SIZE) + 1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Control Interface (Simplified for Testing)
    //=========================================================================
    // Read request control
    input  logic                        datard_valid,           // Start read operation
    output logic                        datard_ready,           // Ready to accept request
    input  logic [ADDR_WIDTH-1:0]       datard_addr,            // Source address
    input  logic [31:0]                 datard_beats_remaining, // Total beats to read
    input  logic [7:0]                  datard_burst_len,       // Burst length
    input  logic [3:0]                  datard_channel_id,      // Channel ID (0-7)

    // Completion status
    output logic                        datard_done_strobe,     // Read burst completed
    output logic [31:0]                 datard_beats_done,      // Beats completed
    output logic                        datard_error,           // Read error
    output logic [1:0]                  datard_error_resp,      // AXI error response

    //=========================================================================
    // AXI4 Read Interface (to Memory Model)
    //=========================================================================
    // AR Channel
    output logic [ID_WIDTH-1:0]         m_axi_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // R Channel
    input  logic [ID_WIDTH-1:0]         m_axi_rid,
    input  logic [DATA_WIDTH-1:0]       m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    //=========================================================================
    // SRAM Status Outputs (for Monitoring)
    //=========================================================================
    output logic [NUM_CHANNELS-1:0]     sram_rd_valid,          // Data available per channel
    output logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] sram_rd_count  // Entries per channel
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // SRAM Controller → AXI Read Engine (R channel data)
    logic                        axi_rd_data_valid;
    logic [ID_WIDTH-1:0]         axi_rd_data_id;
    logic [DATA_WIDTH-1:0]       axi_rd_data;
    logic                        axi_rd_data_ready;

    // SRAM Controller → AXI Read Engine (space pre-allocation)
    logic [NUM_CHANNELS-1:0]     rd_space_req;
    logic [NUM_CHANNELS-1:0][7:0] rd_space_count;
    logic [NUM_CHANNELS-1:0]     rd_space_grant;
    logic [NUM_CHANNELS-1:0]     rd_space_valid;

    // SRAM Controller → SRAM (write path - not used in read-only test, tie off)
    logic [NUM_CHANNELS-1:0]     axi_wr_sram_req;
    logic [NUM_CHANNELS-1:0]     axi_wr_sram_ack;
    logic [NUM_CHANNELS-1:0][DATA_WIDTH-1:0] axi_wr_sram_data;

    // SRAM Physical Interface
    logic                        sram_wr_en;
    logic [SRAM_ADDR_WIDTH-1:0]  sram_wr_addr;
    logic [DATA_WIDTH-1:0]       sram_wr_data;
    logic                        sram_rd_en;
    logic [SRAM_ADDR_WIDTH-1:0]  sram_rd_addr;
    logic [DATA_WIDTH-1:0]       sram_rd_data_out;
    logic                        sram_rd_data_valid;

    // Tie off write path (not used in read-only test)
    assign axi_wr_sram_req = '0;

    // For testing, we'll request space for the entire burst upfront
    // In real design, scheduler handles this
    assign rd_space_req = (datard_valid) ? (1 << datard_channel_id) : '0;
    assign rd_space_count[datard_channel_id] = datard_burst_len;

    //=========================================================================
    // AXI Read Engine Instantiation
    //=========================================================================
    axi_read_engine #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .MAX_BURST_LEN(MAX_BURST_LEN),
        .SRAM_DEPTH(SRAM_DEPTH)
    ) u_axi_read_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Control Interface
        .datard_valid           (datard_valid),
        .datard_ready           (datard_ready),
        .datard_addr            (datard_addr),
        .datard_beats_remaining (datard_beats_remaining),
        .datard_burst_len       (datard_burst_len),
        .datard_channel_id      (datard_channel_id),

        // Completion
        .datard_done_strobe     (datard_done_strobe),
        .datard_beats_done      (datard_beats_done),
        .datard_error           (datard_error),
        .datard_error_resp      (datard_error_resp),

        // AXI4 AR Channel
        .m_axi_arid             (m_axi_arid),
        .m_axi_araddr           (m_axi_araddr),
        .m_axi_arlen            (m_axi_arlen),
        .m_axi_arsize           (m_axi_arsize),
        .m_axi_arburst          (m_axi_arburst),
        .m_axi_arvalid          (m_axi_arvalid),
        .m_axi_arready          (m_axi_arready),

        // AXI4 R Channel
        .m_axi_rid              (m_axi_rid),
        .m_axi_rdata            (m_axi_rdata),
        .m_axi_rresp            (m_axi_rresp),
        .m_axi_rlast            (m_axi_rlast),
        .m_axi_rvalid           (m_axi_rvalid),
        .m_axi_rready           (m_axi_rready),

        // To SRAM Controller
        .sram_wr_valid          (axi_rd_data_valid),
        .sram_wr_id             (axi_rd_data_id),
        .sram_wr_data           (axi_rd_data),
        .sram_wr_ready          (axi_rd_data_ready)
    );

    //=========================================================================
    // SRAM Controller Instantiation
    //=========================================================================
    sram_controller #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .SRAM_DEPTH(SRAM_DEPTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) u_sram_controller (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // AXI Read Data Interface (Write to SRAM)
        .axi_rd_data_valid      (axi_rd_data_valid),
        .axi_rd_data_id         (axi_rd_data_id),
        .axi_rd_data            (axi_rd_data),
        .axi_rd_data_ready      (axi_rd_data_ready),

        // Pre-allocation Interface
        .rd_space_req           (rd_space_req),
        .rd_xfer_count          (rd_space_count),
        .rd_space_grant         (rd_space_grant),
        .rd_space_valid         (rd_space_valid),

        // AXI Write Data Interface (Read from SRAM) - Tied off
        .axi_wr_sram_req        (axi_wr_sram_req),
        .axi_wr_sram_ack        (axi_wr_sram_ack),
        .axi_wr_sram_data       (axi_wr_sram_data),

        // Flow Control
        .sram_rd_valid          (sram_rd_valid),
        .sram_rd_count          (sram_rd_count),

        // SRAM Physical Interface
        .sram_wr_en             (sram_wr_en),
        .sram_wr_addr           (sram_wr_addr),
        .sram_wr_data           (sram_wr_data),
        .sram_rd_en             (sram_rd_en),
        .sram_rd_addr           (sram_rd_addr),
        .sram_rd_data           (sram_rd_data_out),
        .sram_rd_data_valid     (sram_rd_data_valid)
    );

    //=========================================================================
    // SRAM Instantiation
    //=========================================================================
    simple_sram #(
        .ADDR_WIDTH(SRAM_ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(SRAM_DEPTH)
    ) u_simple_sram (
        .clk                    (clk),

        // Write port (from SRAM Controller)
        .wr_en                  (sram_wr_en),
        .wr_addr                (sram_wr_addr),
        .wr_data                (sram_wr_data),
        .wr_chunk_en            ('1),  // Write all chunks

        // Read port (to SRAM Controller)
        .rd_en                  (sram_rd_en),
        .rd_addr                (sram_rd_addr),
        .rd_data                (sram_rd_data_out)
    );

    // SRAM read data valid (1-cycle latency)
    logic sram_rd_en_q;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            sram_rd_en_q <= 1'b0;
        end else begin
            sram_rd_en_q <= sram_rd_en;
        end
    )
    assign sram_rd_data_valid = sram_rd_en_q;

endmodule : datapath_rd_test
