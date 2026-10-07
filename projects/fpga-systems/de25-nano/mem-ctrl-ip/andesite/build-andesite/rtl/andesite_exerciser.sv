// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_exerciser
// Purpose: On-chip AXI4 traffic generator for the andesite skeleton build.
//          After init completes it loops write-burst/read-burst pairs across
//          the bank-address stride, so every datapath the idle build folded
//          away -- write CAM fill/drain, write-data CDC, serializer, read
//          return ring, aligner -- toggles for real and the timing report
//          covers the whole core. No error checking (there is no DRAM to be
//          wrong against); traffic shape is the entire point.
//
//          Burst: 8 x 16-byte beats (AWLEN=7, AWSIZE=4, INCR) at an address
//          stepping by the DDR4 bank stride (2^(COL_WIDTH + 4) = 16 KiB at
//          this geometry), so consecutive bursts land in different banks
//          and the bank timers / arbiter see real rotation.

`timescale 1ns / 1ps

module andesite_exerciser #(
    parameter int AW = 32,
    parameter int DW = 128,
    parameter int IW = 8,
    parameter int COLW = 10,              // column bits (bank stride derives)
    parameter int BANK_STRIDE = (1 << (COLW + 4))
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        enable_i,         // high once init has completed

    // ---- AXI4 master ----
    output logic [IW-1:0] m_axi_awid,
    output logic [AW-1:0] m_axi_awaddr,
    output logic [7:0]    m_axi_awlen,
    output logic [2:0]    m_axi_awsize,
    output logic [1:0]    m_axi_awburst,
    output logic          m_axi_awvalid,
    input  logic          m_axi_awready,
    output logic [DW-1:0] m_axi_wdata,
    output logic [DW/8-1:0] m_axi_wstrb,
    output logic          m_axi_wlast,
    output logic          m_axi_wvalid,
    input  logic          m_axi_wready,
    input  logic [IW-1:0] m_axi_bid,
    input  logic [1:0]    m_axi_bresp,
    input  logic          m_axi_bvalid,
    output logic          m_axi_bready,
    output logic [IW-1:0] m_axi_arid,
    output logic [AW-1:0] m_axi_araddr,
    output logic [7:0]    m_axi_arlen,
    output logic [2:0]    m_axi_arsize,
    output logic [1:0]    m_axi_arburst,
    output logic          m_axi_arvalid,
    input  logic          m_axi_arready,
    input  logic [IW-1:0] m_axi_rid,
    input  logic [DW-1:0] m_axi_rdata,
    input  logic [1:0]    m_axi_rresp,
    input  logic          m_axi_rlast,
    input  logic          m_axi_rvalid,
    output logic          m_axi_rready,
    output logic          exerciser_busy_o
);

    typedef enum logic [2:0] {
        ST_IDLE,
        ST_AW,
        ST_W,
        ST_B,
        ST_AR,
        ST_R
    } state_e;

    state_e state;
    logic [AW-1:0] addr;
    logic [3:0]    beat;          // burst position 0..7
    logic [63:0]   wpat;          // walking data pattern

    wire [AW-1:0] addr_next = addr + BANK_STRIDE;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= ST_IDLE;
            addr    <= '0;
            beat    <= '0;
            wpat    <= 64'hdead_beef_0000_0001;
        end else begin
            case (state)
                ST_IDLE: if (enable_i) begin
                    addr  <= '0;
                    state <= ST_AW;
                end

                ST_AW: if (m_axi_awvalid && m_axi_awready) begin
                    beat  <= '0;
                    state <= ST_W;
                end

                ST_W: if (m_axi_wvalid && m_axi_wready) begin
                    wpat <= {wpat[62:0], wpat[63] ^ wpat[62] ^ wpat[60] ^ wpat[59]};
                    if (m_axi_wlast) state <= ST_B;
                    beat <= beat + 1'b1;
                end

                ST_B: if (m_axi_bvalid && m_axi_bready) state <= ST_AR;

                ST_AR: if (m_axi_arvalid && m_axi_arready) begin
                    beat  <= '0;
                    state <= ST_R;
                end

                ST_R: if (m_axi_rvalid && m_axi_rready && m_axi_rlast) begin
                    addr  <= addr_next;
                    state <= ST_AW;      // back-to-back: no idle gap
                end

                default: state <= ST_IDLE;
            endcase
        end
    end

    // ---- channel drives --------------------------------------------------
    assign m_axi_awid    = '0;
    assign m_axi_awaddr  = addr;
    assign m_axi_awlen   = 8'd7;        // 8 beats
    assign m_axi_awsize  = 3'd4;        // 16 bytes per beat (= the DFI word)
    assign m_axi_awburst = 2'b01;       // INCR
    assign m_axi_awvalid = (state == ST_AW);

    assign m_axi_wdata   = {2{wpat}};
    assign m_axi_wstrb   = '1;
    assign m_axi_wlast   = (beat == 4'd7);
    assign m_axi_wvalid  = (state == ST_W);

    assign m_axi_bready  = (state == ST_B);

    assign m_axi_arid    = '0;
    assign m_axi_araddr  = addr;
    assign m_axi_arlen   = 8'd7;
    assign m_axi_arsize  = 3'd4;
    assign m_axi_arburst = 2'b01;
    assign m_axi_arvalid = (state == ST_AR);

    assign m_axi_rready  = (state == ST_R);

    assign exerciser_busy_o = (state != ST_IDLE);

endmodule : andesite_exerciser
