// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_read_engine
// Purpose: AXI4 Read Engine - Streaming Pipeline (NO FSM!)
//
// Description:
//   High-performance streaming AXI4 read engine with NO FSM.
//   Uses arbiter-granted access and continuous streaming for max performance.
//
// Version 1 - Basic:
//   - Single outstanding read transaction
//   - Fixed or requested burst length
//   - Streaming pipeline (no FSM stalls)
//
// Key Insight:
//   FSMs are horrible for performance! This design uses:
//   - Arbiter grants channel access
//   - Streaming pipeline moves data continuously when granted
//   - datard_* interface controls flow (no FSM needed!)
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


module axi_read_engine #(
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

    // Data Read Interface (from Scheduler via Arbiter)
    input  logic                        datard_valid,           // Channel requesting read
    output logic                        datard_ready,           // Engine ready for request
    input  logic [ADDR_WIDTH-1:0]       datard_addr,            // Source address (aligned)
    input  logic [31:0]                 datard_beats_remaining, // Total beats left to read
    input  logic [7:0]                  datard_burst_len,       // Requested burst length
    input  logic [3:0]                  datard_channel_id,      // Channel ID for tracking

    // Completion Strobes (back to Scheduler)
    output logic                        datard_done_strobe,     // Read burst completed
    output logic [31:0]                 datard_beats_done,      // Beats completed this cycle

    // Error Signals
    output logic                        datard_error,           // Read error occurred
    output logic [1:0]                  datard_error_resp,      // AXI response (SLVERR/DECERR)

    // AXI4 AR Channel (Read Address)
    output logic [ID_WIDTH-1:0]         m_axi_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,            // Burst length - 1
    output logic [2:0]                  m_axi_arsize,           // Burst size (log2(bytes))
    output logic [1:0]                  m_axi_arburst,          // Burst type (INCR)
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // AXI4 R Channel (Read Data)
    input  logic [ID_WIDTH-1:0]         m_axi_rid,
    input  logic [DATA_WIDTH-1:0]       m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    // SRAM Write Interface
    output logic                        sram_wr_en,
    output logic [SRAM_ADDR_WIDTH-1:0]  sram_wr_addr,
    output logic [DATA_WIDTH-1:0]       sram_wr_data,
    input  logic                        sram_wr_ready           // SRAM can accept write
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int BYTES_PER_BEAT = DATA_WIDTH / 8;
    localparam int AXSIZE = $clog2(BYTES_PER_BEAT);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // AR Channel Management
    logic [ADDR_WIDTH-1:0] r_ar_addr;
    logic [7:0] r_ar_len;
    logic [3:0] r_ar_channel_id;
    logic r_ar_valid;
    logic r_ar_inflight;

    // R Channel Management
    logic [7:0] r_beats_received;
    logic [7:0] r_expected_beats;
    logic r_error_detected;
    logic [1:0] r_error_resp;

    // SRAM Write Management
    logic [SRAM_ADDR_WIDTH-1:0] r_sram_wr_ptr;

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
        w_burst_len = datard_burst_len;

        // Cap to remaining beats
        if (datard_beats_remaining < {24'h0, w_burst_len}) begin
            w_burst_len = datard_beats_remaining[7:0];
        end

        // Cap to MAX_BURST_LEN
        if (w_burst_len > 8'(MAX_BURST_LEN)) begin
            w_burst_len = 8'(MAX_BURST_LEN);
        end

        // Minimum 1 beat
        if (w_burst_len == 8'h0) begin
            w_burst_len = 8'h1;
        end

        // Convert to AXI arlen (burst_len - 1)
        w_capped_burst_len = w_burst_len - 8'h1;
    end

    //=========================================================================
    // AR Channel Logic (Read Address)
    //=========================================================================
    // Streaming pipeline: Accept new request when not inflight

    assign datard_ready = !r_ar_inflight && !r_ar_valid;

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_ar_addr <= '0;
            r_ar_len <= '0;
            r_ar_channel_id <= '0;
            r_ar_valid <= 1'b0;
            r_ar_inflight <= 1'b0;
        end else begin
            // Accept new request when ready
            if (datard_valid && datard_ready) begin
                r_ar_addr <= datard_addr;
                r_ar_len <= w_capped_burst_len;
                r_ar_channel_id <= datard_channel_id;
                r_ar_valid <= 1'b1;
                r_ar_inflight <= 1'b1;  // Mark transaction inflight
            end

            // AXI AR handshake
            if (r_ar_valid && m_axi_arready) begin
                r_ar_valid <= 1'b0;
            end

            // Clear inflight when last beat received
            if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
                r_ar_inflight <= 1'b0;
            end
        end
    )


    // AXI AR Channel Outputs
    assign m_axi_arid    = {4'h0, r_ar_channel_id};
    assign m_axi_araddr  = r_ar_addr;
    assign m_axi_arlen   = r_ar_len;
    assign m_axi_arsize  = AXSIZE[2:0];
    assign m_axi_arburst = 2'b01;  // INCR
    assign m_axi_arvalid = r_ar_valid;

    //=========================================================================
    // R Channel Logic (Read Data)
    //=========================================================================
    // Streaming pipeline: Receive data continuously, write to SRAM

    // Ready when SRAM can accept write
    assign m_axi_rready = sram_wr_ready;

    // Beat counter tracks progress through burst
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_beats_received <= '0;
            r_expected_beats <= '0;
            r_error_detected <= 1'b0;
            r_error_resp <= 2'b00;
        end else begin
            // Latch expected beats when AR handshakes
            if (r_ar_valid && m_axi_arready) begin
                r_expected_beats <= r_ar_len + 8'h1;  // arlen is (beats - 1)
                r_beats_received <= '0;
            end

            // Count beats as they arrive
            if (m_axi_rvalid && m_axi_rready) begin
                r_beats_received <= r_beats_received + 8'h1;

                // Check for error response
                if (m_axi_rresp != 2'b00) begin  // OKAY = 00
                    r_error_detected <= 1'b1;
                    r_error_resp <= m_axi_rresp;
                end

                // Clear error on last beat
                if (m_axi_rlast) begin
                    r_beats_received <= '0;
                    if (m_axi_rresp == 2'b00) begin
                        r_error_detected <= 1'b0;
                    end
                end
            end
        end
    )


    //=========================================================================
    // SRAM Write Logic
    //=========================================================================
    // Streaming pipeline: Write data directly to SRAM as it arrives

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_sram_wr_ptr <= '0;
        end else begin
            // Write to SRAM when R channel data arrives
            if (m_axi_rvalid && m_axi_rready) begin
                r_sram_wr_ptr <= r_sram_wr_ptr + 1'b1;

                // Wrap SRAM pointer
                if (r_sram_wr_ptr == SRAM_ADDR_WIDTH'(SRAM_DEPTH - 1)) begin
                    r_sram_wr_ptr <= '0;
                end
            end
        end
    )


    // SRAM Write Outputs
    assign sram_wr_en = m_axi_rvalid && m_axi_rready;
    assign sram_wr_addr = r_sram_wr_ptr;
    assign sram_wr_data = m_axi_rdata;

    //=========================================================================
    // Completion Strobe Generation
    //=========================================================================
    // Report back to scheduler when burst completes

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_done_strobe <= 1'b0;
            r_beats_done <= '0;
        end else begin
            // Generate strobe on last beat
            r_done_strobe <= m_axi_rvalid && m_axi_rready && m_axi_rlast;

            if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
                r_beats_done <= {24'h0, r_expected_beats};
            end else begin
                r_beats_done <= '0;
            end
        end
    )


    assign datard_done_strobe = r_done_strobe;
    assign datard_beats_done = r_beats_done;

    //=========================================================================
    // Error Outputs
    //=========================================================================

    assign datard_error = r_error_detected;
    assign datard_error_resp = r_error_resp;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Only one transaction inflight in v1
    property single_inflight;
        @(posedge clk) disable iff (!rst_n)
        r_ar_inflight |-> !datard_ready;
    endproperty
    assert property (single_inflight);

    // Beat counter matches arlen
    property beat_count_match;
        @(posedge clk) disable iff (!rst_n)
        (m_axi_rvalid && m_axi_rready && m_axi_rlast) |->
            (r_beats_received == r_expected_beats);
    endproperty
    assert property (beat_count_match);

    // SRAM write only when R valid
    property sram_write_valid;
        @(posedge clk) disable iff (!rst_n)
        sram_wr_en |-> m_axi_rvalid;
    endproperty
    assert property (sram_write_valid);
    `endif

endmodule : axi_read_engine
