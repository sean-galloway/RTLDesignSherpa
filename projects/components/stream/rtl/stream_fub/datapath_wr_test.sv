// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: datapath_wr_test
// Purpose: Write Data Path Test Wrapper (SRAM → SRAM Controller → AXI Write)
//
// Description:
//   Integration test wrapper for validating the write data path streaming performance.
//   Tests data flow from SRAM buffer through SRAM Controller to AXI write transactions.
//
//   Data Flow:
//     SRAM Buffer → SRAM Controller → AXI Write Engine → AXI Slave (Memory)
//
//   Key Validation Points:
//     - SRAM Controller read path performance
//     - AXI AW/W/B channel streaming without backpressure
//     - Buffer management and flow control
//     - No stalls under continuous streaming
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-10-26

`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module datapath_wr_test #(
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
    // Write request control
    input  logic                        datawr_valid,           // Start write operation
    output logic                        datawr_ready,           // Ready to accept request
    input  logic [ADDR_WIDTH-1:0]       datawr_addr,            // Destination address
    input  logic [31:0]                 datawr_beats_remaining, // Total beats to write
    input  logic [7:0]                  datawr_burst_len,       // Burst length
    input  logic [3:0]                  datawr_channel_id,      // Channel ID (0-7)

    // Completion status
    output logic                        datawr_done_strobe,     // Write burst completed
    output logic [31:0]                 datawr_beats_done,      // Beats completed
    output logic                        datawr_error,           // Write error
    output logic [1:0]                  datawr_error_resp,      // AXI error response

    //=========================================================================
    // AXI4 Write Interface (to Memory Model)
    //=========================================================================
    // AW Channel
    output logic [ID_WIDTH-1:0]         m_axi_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // W Channel
    output logic [DATA_WIDTH-1:0]       m_axi_wdata,
    output logic [(DATA_WIDTH/8)-1:0]   m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // B Channel
    input  logic [ID_WIDTH-1:0]         m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    //=========================================================================
    // SRAM Preload Interface (for Test Setup)
    //=========================================================================
    input  logic                        sram_preload_en,        // Preload enable
    input  logic [SRAM_ADDR_WIDTH-1:0]  sram_preload_addr,      // Preload address
    input  logic [DATA_WIDTH-1:0]       sram_preload_data,      // Preload data

    //=========================================================================
    // SRAM Status Outputs (for Monitoring)
    //=========================================================================
    output logic [NUM_CHANNELS-1:0]     sram_wr_valid,          // Space available per channel
    output logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] sram_wr_count  // Free space per channel
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // SRAM Controller → AXI Write Engine (Write data request)
    logic [NUM_CHANNELS-1:0]     axi_wr_sram_req;
    logic [NUM_CHANNELS-1:0]     axi_wr_sram_ack;
    logic [NUM_CHANNELS-1:0][DATA_WIDTH-1:0] axi_wr_sram_data;

    // SRAM Controller → AXI Read Engine (not used in write-only test, tie off)
    logic                        axi_rd_data_valid;
    logic [ID_WIDTH-1:0]         axi_rd_data_id;
    logic [DATA_WIDTH-1:0]       axi_rd_data;
    logic                        axi_rd_data_ready;
    logic [NUM_CHANNELS-1:0]     rd_space_req;
    logic [NUM_CHANNELS-1:0][7:0] rd_space_count;
    logic [NUM_CHANNELS-1:0]     rd_space_grant;
    logic [NUM_CHANNELS-1:0]     rd_space_valid;

    // SRAM Physical Interface
    logic                        sram_wr_en;
    logic [SRAM_ADDR_WIDTH-1:0]  sram_wr_addr;
    logic [DATA_WIDTH-1:0]       sram_wr_data;
    logic                        sram_rd_en;
    logic [SRAM_ADDR_WIDTH-1:0]  sram_rd_addr;
    logic [DATA_WIDTH-1:0]       sram_rd_data_out;
    logic                        sram_rd_data_valid;

    // SRAM Read Logic (for AXI Write Engine)
    logic sram_rd_en_q;

    // Tie off read path (not used in write-only test)
    assign axi_rd_data_valid = '0;
    assign rd_space_req = '0;

    // For testing, connect write request directly to SRAM controller
    assign axi_wr_sram_req = (datawr_valid) ? (1 << datawr_channel_id) : '0;

    //=========================================================================
    // AXI Write Engine Instantiation
    //=========================================================================
    axi_write_engine #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .MAX_BURST_LEN(MAX_BURST_LEN),
        .SRAM_DEPTH(SRAM_DEPTH)
    ) u_axi_write_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Control Interface
        .datawr_valid           (datawr_valid),
        .datawr_ready           (datawr_ready),
        .datawr_addr            (datawr_addr),
        .datawr_beats_remaining (datawr_beats_remaining),
        .datawr_burst_len       (datawr_burst_len),
        .datawr_channel_id      (datawr_channel_id),

        // Completion
        .datawr_done_strobe     (datawr_done_strobe),
        .datawr_beats_done      (datawr_beats_done),
        .datawr_error           (datawr_error),
        .datawr_error_resp      (datawr_error_resp),

        // AXI4 AW Channel
        .m_axi_awid             (m_axi_awid),
        .m_axi_awaddr           (m_axi_awaddr),
        .m_axi_awlen            (m_axi_awlen),
        .m_axi_awsize           (m_axi_awsize),
        .m_axi_awburst          (m_axi_awburst),
        .m_axi_awvalid          (m_axi_awvalid),
        .m_axi_awready          (m_axi_awready),

        // AXI4 W Channel
        .m_axi_wdata            (m_axi_wdata),
        .m_axi_wstrb            (m_axi_wstrb),
        .m_axi_wlast            (m_axi_wlast),
        .m_axi_wvalid           (m_axi_wvalid),
        .m_axi_wready           (m_axi_wready),

        // AXI4 B Channel
        .m_axi_bid              (m_axi_bid),
        .m_axi_bresp            (m_axi_bresp),
        .m_axi_bvalid           (m_axi_bvalid),
        .m_axi_bready           (m_axi_bready),

        // SRAM Read Interface
        .sram_rd_en             (sram_rd_en),
        .sram_rd_addr           (sram_rd_addr),
        .sram_rd_data           (sram_rd_data_out),
        .sram_rd_valid          (sram_rd_data_valid)
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

        // AXI Read Data Interface (Write to SRAM) - Tied off
        .axi_rd_data_valid      (axi_rd_data_valid),
        .axi_rd_data_id         (axi_rd_data_id),
        .axi_rd_data            (axi_rd_data),
        .axi_rd_data_ready      (axi_rd_data_ready),

        // Pre-allocation Interface - Tied off
        .rd_space_req           (rd_space_req),
        .rd_xfer_count          (rd_space_count),
        .rd_space_grant         (rd_space_grant),
        .rd_space_valid         (rd_space_valid),

        // AXI Write Data Interface (Read from SRAM)
        .axi_wr_sram_req        (axi_wr_sram_req),
        .axi_wr_sram_ack        (axi_wr_sram_ack),
        .axi_wr_sram_data       (axi_wr_sram_data),

        // Flow Control
        .sram_rd_valid          (sram_wr_valid),        // Inverted naming: write=space avail
        .sram_rd_count          (sram_wr_count),

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
    // SRAM Instantiation with Preload Support
    //=========================================================================
    // MUX between normal operation and preload
    logic                        sram_wr_en_mux;
    logic [SRAM_ADDR_WIDTH-1:0]  sram_wr_addr_mux;
    logic [DATA_WIDTH-1:0]       sram_wr_data_mux;

    assign sram_wr_en_mux   = sram_preload_en ? sram_preload_en : sram_wr_en;
    assign sram_wr_addr_mux = sram_preload_en ? sram_preload_addr : sram_wr_addr;
    assign sram_wr_data_mux = sram_preload_en ? sram_preload_data : sram_wr_data;

    simple_sram #(
        .ADDR_WIDTH(SRAM_ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(SRAM_DEPTH)
    ) u_simple_sram (
        .clk                    (clk),

        // Write port (MUXed: preload or normal)
        .wr_en                  (sram_wr_en_mux),
        .wr_addr                (sram_wr_addr_mux),
        .wr_data                (sram_wr_data_mux),
        .wr_chunk_en            ('1),  // Write all chunks

        // Read port (to AXI Write Engine via SRAM Controller)
        .rd_en                  (sram_rd_en),
        .rd_addr                (sram_rd_addr),
        .rd_data                (sram_rd_data_out)
    );

    // SRAM read data valid (1-cycle latency)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            sram_rd_en_q <= 1'b0;
        end else begin
            sram_rd_en_q <= sram_rd_en;
        end
    )
    assign sram_rd_data_valid = sram_rd_en_q;

endmodule : datapath_wr_test
