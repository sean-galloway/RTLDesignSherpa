// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: wb4_master_slave_loop
// Purpose: Test collateral only. A wb4_master wired to a wb4_slave so the
//          pair is driven and checked entirely through their FUB-side
//          valid/ready queues with the GAXI BFMs, and the Wishbone wires in
//          between are checked by the protocol assertions below.
//
// Subsystem: amba (testcode)
// Author: sean galloway
// Created: 2026-09-09

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_master_slave_loop
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int M_CMD_DEPTH     = 4,
    parameter int M_RSP_DEPTH     = 4,
    parameter int S_CMD_DEPTH     = 2,
    parameter int S_RSP_DEPTH     = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DATA_WIDTH / 8,
    parameter int STW = WB4_STATUS_WIDTH
) (
    input  logic              clk,
    input  logic              aresetn,

    // Master FUB side (the BFMs drive commands in, take responses out)
    input  logic              m_cmd_valid,
    output logic              m_cmd_ready,
    input  logic              m_cmd_we,
    input  logic [AW-1:0]     m_cmd_adr,
    input  logic [DW-1:0]     m_cmd_dat,
    input  logic [SW-1:0]     m_cmd_sel,
    output logic              m_rsp_valid,
    input  logic              m_rsp_ready,
    output logic [STW-1:0]    m_rsp_status,
    output logic [DW-1:0]     m_rsp_dat,

    // Slave FUB side (the BFMs take commands out, drive responses in)
    output logic              s_cmd_valid,
    input  logic              s_cmd_ready,
    output logic              s_cmd_we,
    output logic [AW-1:0]     s_cmd_adr,
    output logic [DW-1:0]     s_cmd_dat,
    output logic [SW-1:0]     s_cmd_sel,
    input  logic              s_rsp_valid,
    output logic              s_rsp_ready,
    input  logic [STW-1:0]    s_rsp_status,
    input  logic [DW-1:0]     s_rsp_dat,

    // The Wishbone wires, exposed for the testbench's protocol checks
    output logic              wb_CYC,
    output logic              wb_STB,
    output logic              wb_WE,
    output logic [AW-1:0]     wb_ADR,
    output logic [DW-1:0]     wb_DAT_W,
    output logic [SW-1:0]     wb_SEL,
    output logic              wb_STALL,
    output logic              wb_ACK,
    output logic              wb_ERR,
    output logic              wb_RTY,
    output logic [DW-1:0]     wb_DAT_R
);

    wb4_master #(
        .ADDR_WIDTH (AW), .DATA_WIDTH (DW),
        .CMD_DEPTH  (M_CMD_DEPTH), .RSP_DEPTH (M_RSP_DEPTH)
    ) u_master (
        .clk        (clk),         .aresetn    (aresetn),
        .m_wb_CYC   (wb_CYC),      .m_wb_STB   (wb_STB),
        .m_wb_WE    (wb_WE),       .m_wb_ADR   (wb_ADR),
        .m_wb_DAT_W (wb_DAT_W),    .m_wb_SEL   (wb_SEL),
        .m_wb_STALL (wb_STALL),    .m_wb_ACK   (wb_ACK),
        .m_wb_ERR   (wb_ERR),      .m_wb_RTY   (wb_RTY),
        .m_wb_DAT_R (wb_DAT_R),
        .cmd_valid  (m_cmd_valid), .cmd_ready  (m_cmd_ready),
        .cmd_we     (m_cmd_we),    .cmd_adr    (m_cmd_adr),
        .cmd_dat    (m_cmd_dat),   .cmd_sel    (m_cmd_sel),
        .rsp_valid  (m_rsp_valid), .rsp_ready  (m_rsp_ready),
        .rsp_status (m_rsp_status),.rsp_dat    (m_rsp_dat)
    );

    wb4_slave #(
        .ADDR_WIDTH (AW), .DATA_WIDTH (DW),
        .CMD_DEPTH  (S_CMD_DEPTH), .RSP_DEPTH (S_RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING)
    ) u_slave (
        .clk        (clk),         .aresetn    (aresetn),
        .s_wb_CYC   (wb_CYC),      .s_wb_STB   (wb_STB),
        .s_wb_WE    (wb_WE),       .s_wb_ADR   (wb_ADR),
        .s_wb_DAT_W (wb_DAT_W),    .s_wb_SEL   (wb_SEL),
        .s_wb_STALL (wb_STALL),    .s_wb_ACK   (wb_ACK),
        .s_wb_ERR   (wb_ERR),      .s_wb_RTY   (wb_RTY),
        .s_wb_DAT_R (wb_DAT_R),
        .cmd_valid  (s_cmd_valid), .cmd_ready  (s_cmd_ready),
        .cmd_we     (s_cmd_we),    .cmd_adr    (s_cmd_adr),
        .cmd_dat    (s_cmd_dat),   .cmd_sel    (s_cmd_sel),
        .rsp_valid  (s_rsp_valid), .rsp_ready  (s_rsp_ready),
        .rsp_status (s_rsp_status),.rsp_dat    (s_rsp_dat)
    );

    // ------------------------------------------------------------------------
    // Wishbone B4 pipelined protocol checks on the wires between the two.
    // These are what a Wishbone BFM monitor would check; until one exists in
    // the framework they live here, in test collateral, not in the blocks.
    // ------------------------------------------------------------------------
    logic           r_stb_q, r_stall_q, r_cyc_q, r_we_q;
    logic [AW-1:0]  r_adr_q;
    logic [DW-1:0]  r_dat_q;
    logic [SW-1:0]  r_sel_q;
    int             accepted, terminated;   // for the testbench to read
    int             violations;
    int             max_inflight;           // peak accepted-not-terminated: proves pipelining

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_stb_q <= 1'b0; r_stall_q <= 1'b0; r_cyc_q <= 1'b0; r_we_q <= 1'b0;
            r_adr_q <= '0; r_dat_q <= '0; r_sel_q <= '0;
            accepted <= 0; terminated <= 0; violations <= 0; max_inflight <= 0;
        end else begin
            r_stb_q <= wb_STB; r_stall_q <= wb_STALL; r_cyc_q <= wb_CYC; r_we_q <= wb_WE;
            r_adr_q <= wb_ADR; r_dat_q <= wb_DAT_W; r_sel_q <= wb_SEL;
            if (wb_CYC && wb_STB && !wb_STALL) accepted <= accepted + 1;
            if (wb_ACK || wb_ERR || wb_RTY)    terminated <= terminated + 1;
            if (accepted - terminated > max_inflight) max_inflight <= accepted - terminated;

            // STB without CYC
            if (wb_STB && !wb_CYC) begin
                violations <= violations + 1;
                $error("%m WB: STB asserted without CYC");
            end
            // A stalled request must be held, unchanged, until accepted
            if (r_stb_q && r_stall_q && r_cyc_q) begin
                if (!wb_STB || wb_WE != r_we_q || wb_ADR != r_adr_q ||
                    wb_SEL != r_sel_q || (wb_WE && wb_DAT_W != r_dat_q)) begin
                    violations <= violations + 1;
                    $error("%m WB: request changed or dropped while STALLed");
                end
            end
            // At most one termination per clock, only inside a cycle
            if ((wb_ACK + wb_ERR + wb_RTY) > 1) begin
                violations <= violations + 1;
                $error("%m WB: more than one of ACK/ERR/RTY in one clock");
            end
            if ((wb_ACK || wb_ERR || wb_RTY) && !r_cyc_q) begin
                violations <= violations + 1;
                $error("%m WB: termination outside a cycle");
            end
            // Never more terminations than accepted requests
            if (terminated + int'(wb_ACK || wb_ERR || wb_RTY) >
                accepted + int'(wb_CYC && wb_STB && !wb_STALL)) begin
                violations <= violations + 1;
                $error("%m WB: termination without an accepted request");
            end
        end
    )

endmodule : wb4_master_slave_loop
