// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_write_engine
// Purpose: AXI4 Write Engine - Streaming Pipeline (NO FSM!)
//
// Description:
//   High-performance streaming AXI4 write engine with NO FSM.
//   Uses arbiter-granted access and continuous streaming for max performance.
//
// Version 1 - Basic:
//   - Single outstanding write transaction
//   - Fixed or requested burst length
//   - Streaming pipeline (no FSM stalls)
//
// Key Insight:
//   FSMs are horrible for performance! This design uses:
//   - Arbiter grants channel access
//   - Streaming pipeline moves data continuously when granted
//   - datawr_* interface controls flow (no FSM needed!)
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"


module axi_write_engine #(
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int ID_WIDTH = 8,
    parameter int MAX_BURST_LEN = 16,         // Maximum AXI burst length
    parameter int SRAM_DEPTH = 4096,
    parameter int SRAM_ADDR_WIDTH = $clog2(SRAM_DEPTH)
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Data Write Interface (from Scheduler via Arbiter)
    input  logic                        datawr_valid,           // Channel requesting write
    output logic                        datawr_ready,           // Engine ready for request
    input  logic [ADDR_WIDTH-1:0]       datawr_addr,            // Destination address (aligned)
    input  logic [31:0]                 datawr_beats_remaining, // Total beats left to write
    input  logic [7:0]                  datawr_burst_len,       // Requested burst length
    input  logic [3:0]                  datawr_channel_id,      // Channel ID for tracking

    // Completion Strobes (back to Scheduler)
    output logic                        datawr_done_strobe,     // Write burst completed
    output logic [31:0]                 datawr_beats_done,      // Beats completed this cycle

    // Error Signals
    output logic                        datawr_error,           // Write error occurred
    output logic [1:0]                  datawr_error_resp,      // AXI response (SLVERR/DECERR)

    // AXI4 AW Channel (Write Address)
    output logic [ID_WIDTH-1:0]         m_axi_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,            // Burst length - 1
    output logic [2:0]                  m_axi_awsize,           // Burst size (log2(bytes))
    output logic [1:0]                  m_axi_awburst,          // Burst type (INCR)
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // AXI4 W Channel (Write Data)
    output logic [DATA_WIDTH-1:0]       m_axi_wdata,
    output logic [(DATA_WIDTH/8)-1:0]   m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // AXI4 B Channel (Write Response)
    input  logic [ID_WIDTH-1:0]         m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    // SRAM Read Interface
    output logic                        sram_rd_en,
    output logic [SRAM_ADDR_WIDTH-1:0]  sram_rd_addr,
    input  logic [DATA_WIDTH-1:0]       sram_rd_data,
    input  logic                        sram_rd_valid           // SRAM data valid
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int BYTES_PER_BEAT = DATA_WIDTH / 8;
    localparam int AXSIZE = $clog2(BYTES_PER_BEAT);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // AW Channel Management
    logic [ADDR_WIDTH-1:0] r_aw_addr;
    logic [7:0] r_aw_len;
    logic [3:0] r_aw_channel_id;
    logic r_aw_valid;
    logic r_aw_inflight;

    // W Channel Management
    logic [7:0] r_beats_sent;
    logic [7:0] r_expected_beats;
    logic r_w_active;

    // B Channel Management
    logic r_b_pending;
    logic r_error_detected;
    logic [1:0] r_error_resp;

    // SRAM Read Management
    logic [SRAM_ADDR_WIDTH-1:0] r_sram_rd_ptr;
    logic r_sram_rd_req;

    // Completion Tracking
    logic r_done_strobe;
    logic [31:0] r_beats_done;

    // Burst Length Calculation
    logic [7:0] w_burst_len;
    logic [7:0] w_capped_burst_len;

    //=========================================================================
    // Burst Length Calculation
    //=========================================================================
    // Engine decides burst length based on:
    // 1. Requested burst length from scheduler
    // 2. Remaining beats
    // 3. MAX_BURST_LEN limit

    always_comb begin
        // Start with requested burst length
        w_burst_len = datawr_burst_len;

        // Cap to remaining beats
        if (datawr_beats_remaining < {24'h0, w_burst_len}) begin
            w_burst_len = datawr_beats_remaining[7:0];
        end

        // Cap to MAX_BURST_LEN
        if (w_burst_len > 8'(MAX_BURST_LEN)) begin
            w_burst_len = 8'(MAX_BURST_LEN);
        end

        // Minimum 1 beat
        if (w_burst_len == 8'h0) begin
            w_burst_len = 8'h1;
        end

        // Convert to AXI awlen (burst_len - 1)
        w_capped_burst_len = w_burst_len - 8'h1;
    end

    //=========================================================================
    // AW Channel Logic (Write Address)
    //=========================================================================
    // Streaming pipeline: Accept new request when not inflight

    assign datawr_ready = !r_aw_inflight && !r_aw_valid && !r_b_pending;

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_aw_addr <= '0;
            r_aw_len <= '0;
            r_aw_channel_id <= '0;
            r_aw_valid <= 1'b0;
            r_aw_inflight <= 1'b0;
        end else begin
            // Accept new request when ready
            if (datawr_valid && datawr_ready) begin
                r_aw_addr <= datawr_addr;
                r_aw_len <= w_capped_burst_len;
                r_aw_channel_id <= datawr_channel_id;
                r_aw_valid <= 1'b1;
                r_aw_inflight <= 1'b1;  // Mark transaction inflight
            end

            // AXI AW handshake
            if (r_aw_valid && m_axi_awready) begin
                r_aw_valid <= 1'b0;
            end

            // Clear inflight when B response received
            if (m_axi_bvalid && m_axi_bready) begin
                r_aw_inflight <= 1'b0;
            end
        end
    )


    // AXI AW Channel Outputs
    assign m_axi_awid    = {4'h0, r_aw_channel_id};
    assign m_axi_awaddr  = r_aw_addr;
    assign m_axi_awlen   = r_aw_len;
    assign m_axi_awsize  = AXSIZE[2:0];
    assign m_axi_awburst = 2'b01;  // INCR
    assign m_axi_awvalid = r_aw_valid;

    //=========================================================================
    // W Channel Logic (Write Data)
    //=========================================================================
    // Streaming pipeline: Read from SRAM, send data continuously

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_beats_sent <= '0;
            r_expected_beats <= '0;
            r_w_active <= 1'b0;
        end else begin
            // Start W phase when AW handshakes
            if (r_aw_valid && m_axi_awready) begin
                r_expected_beats <= r_aw_len + 8'h1;  // awlen is (beats - 1)
                r_beats_sent <= '0;
                r_w_active <= 1'b1;
            end

            // Send beats as SRAM data becomes available
            if (r_w_active && m_axi_wvalid && m_axi_wready) begin
                r_beats_sent <= r_beats_sent + 8'h1;

                // End W phase on last beat
                if (m_axi_wlast) begin
                    r_w_active <= 1'b0;
                    r_beats_sent <= '0;
                end
            end
    )

    end

    // SRAM Read Request
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_sram_rd_req <= 1'b0;
        end else begin
            // Request SRAM read one cycle before W transfer
            r_sram_rd_req <= r_w_active && (r_beats_sent < r_expected_beats);
        end
    )


    // AXI W Channel Outputs
    assign m_axi_wvalid = r_w_active && sram_rd_valid;
    assign m_axi_wdata  = sram_rd_data;
    assign m_axi_wstrb  = {(DATA_WIDTH/8){1'b1}};  // All bytes valid
    assign m_axi_wlast  = (r_beats_sent == (r_expected_beats - 8'h1));

    //=========================================================================
    // SRAM Read Logic
    //=========================================================================
    // Streaming pipeline: Read data from SRAM as needed for W channel

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_sram_rd_ptr <= '0;
        end else begin
            // Read from SRAM when W channel can accept data
            if (r_sram_rd_req) begin
                r_sram_rd_ptr <= r_sram_rd_ptr + 1'b1;

                // Wrap SRAM pointer
                if (r_sram_rd_ptr == SRAM_ADDR_WIDTH'(SRAM_DEPTH - 1)) begin
                    r_sram_rd_ptr <= '0;
                end
            end
        end
    )


    // SRAM Read Outputs
    assign sram_rd_en = r_sram_rd_req;
    assign sram_rd_addr = r_sram_rd_ptr;

    //=========================================================================
    // B Channel Logic (Write Response)
    //=========================================================================
    // Streaming pipeline: Accept response, check for errors

    assign m_axi_bready = 1'b1;  // Always ready for response

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_b_pending <= 1'b0;
            r_error_detected <= 1'b0;
            r_error_resp <= 2'b00;
        end else begin
            // B pending when W last sent
            if (m_axi_wvalid && m_axi_wready && m_axi_wlast) begin
                r_b_pending <= 1'b1;
            end

            // B response received
            if (m_axi_bvalid && m_axi_bready) begin
                r_b_pending <= 1'b0;

                // Check for error response
                if (m_axi_bresp != 2'b00) begin  // OKAY = 00
                    r_error_detected <= 1'b1;
                    r_error_resp <= m_axi_bresp;
                end else begin
                    r_error_detected <= 1'b0;
                end
            end
        end
    )


    //=========================================================================
    // Completion Strobe Generation
    //=========================================================================
    // Report back to scheduler when burst completes

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_done_strobe <= 1'b0;
            r_beats_done <= '0;
        end else begin
            // Generate strobe on B response
            r_done_strobe <= m_axi_bvalid && m_axi_bready;

            if (m_axi_bvalid && m_axi_bready) begin
                r_beats_done <= {24'h0, r_expected_beats};
            end else begin
                r_beats_done <= '0;
            end
        end
    )


    assign datawr_done_strobe = r_done_strobe;
    assign datawr_beats_done = r_beats_done;

    //=========================================================================
    // Error Outputs
    //=========================================================================

    assign datawr_error = r_error_detected;
    assign datawr_error_resp = r_error_resp;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Only one transaction inflight in v1
    property single_inflight;
        @(posedge clk) disable iff (!rst_n)
        r_aw_inflight |-> !datawr_ready;
    endproperty
    assert property (single_inflight);

    // Beat counter matches awlen
    property beat_count_match;
        @(posedge clk) disable iff (!rst_n)
        (m_axi_wvalid && m_axi_wready && m_axi_wlast) |->
            (r_beats_sent == (r_expected_beats - 8'h1));
    endproperty
    assert property (beat_count_match);

    // B response expected after W last
    property b_after_w_last;
        @(posedge clk) disable iff (!rst_n)
        (m_axi_wvalid && m_axi_wready && m_axi_wlast) |=> ##[1:16] m_axi_bvalid;
    endproperty
    assert property (b_after_w_last);

    // SRAM read only when W active
    property sram_read_valid;
        @(posedge clk) disable iff (!rst_n)
        sram_rd_en |-> r_w_active;
    endproperty
    assert property (sram_read_valid);
    `endif

endmodule : axi_write_engine
