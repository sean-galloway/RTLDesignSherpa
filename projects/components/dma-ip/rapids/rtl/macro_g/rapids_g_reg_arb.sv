// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_g_reg_arb
// Purpose: rapids-g (rapids TASK-034): who may push into the register block's
//          command queue. NM masters -- the host's APB and each half's gatling
//          -- share the one cmd/rsp path into peakrdl_to_cmdrsp.
//
// One access is outstanding at a time, as on the host path alone
// (apb4_slave is strictly one-outstanding): a round-robin arbiter
// (arbiter_round_robin_simple_ack) grants one master, its command is passed
// through once, and the grant is held until that master accepts the response
// (the ack), which also steers the response back to it -- the registered
// select the MON-window guard uses.
//
// The masters' addresses come in full width; the instantiation pins each
// gatling to its own half of the register map.
//
// Parameters:
//   - NM: masters (>= 1); master 0 is the host
//   - ADDR_WIDTH, DATA_WIDTH: the cmd/rsp bus
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_g_reg_arb #(
    parameter int NM         = 3,
    parameter int ADDR_WIDTH = 13,
    parameter int DATA_WIDTH = 32,
    parameter int GW         = (NM > 1) ? $clog2(NM) : 1
) (
    input  logic                            clk,
    input  logic                            rst_n,

    // masters
    input  logic [NM-1:0]                   m_cmd_valid,
    output logic [NM-1:0]                   m_cmd_ready,
    input  logic [NM-1:0]                   m_cmd_pwrite,
    input  logic [NM-1:0][ADDR_WIDTH-1:0]   m_cmd_paddr,
    input  logic [NM-1:0][DATA_WIDTH-1:0]   m_cmd_pwdata,
    output logic [NM-1:0]                   m_rsp_valid,
    input  logic [NM-1:0]                   m_rsp_ready,
    output logic [DATA_WIDTH-1:0]           m_rsp_prdata,      // valid for the master with m_rsp_valid
    output logic                            m_rsp_pslverr,

    // the command queue (toward peakrdl_to_cmdrsp)
    output logic                            s_cmd_valid,
    input  logic                            s_cmd_ready,
    output logic                            s_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]           s_cmd_paddr,
    output logic [DATA_WIDTH-1:0]           s_cmd_pwdata,
    input  logic                            s_rsp_valid,
    output logic                            s_rsp_ready,
    input  logic [DATA_WIDTH-1:0]           s_rsp_prdata,
    input  logic                            s_rsp_pslverr
);

    logic          w_gnt_valid;
    logic [NM-1:0] w_gnt;
    logic [GW-1:0] w_gnt_id;
    logic [NM-1:0] w_ack;
    logic          r_cmd_sent;      // the granted master's command has gone

    arbiter_round_robin_simple_ack #(
        .N (NM)
    ) u_arb (
        .clk         (clk),
        .rst_n       (rst_n),
        .request     (m_cmd_valid),
        .grant_ack   (w_ack),
        .grant_valid (w_gnt_valid),
        .grant       (w_gnt),
        .grant_id    (w_gnt_id)
    );

    // Command: the granted master's, once
    assign s_cmd_valid  = w_gnt_valid && !r_cmd_sent && m_cmd_valid[w_gnt_id];
    assign s_cmd_pwrite = m_cmd_pwrite[w_gnt_id];
    assign s_cmd_paddr  = m_cmd_paddr[w_gnt_id];
    assign s_cmd_pwdata = m_cmd_pwdata[w_gnt_id];

    always_comb begin
        m_cmd_ready = '0;
        m_rsp_valid = '0;
        if (w_gnt_valid) begin
            m_cmd_ready[w_gnt_id] = s_cmd_ready && !r_cmd_sent;
            m_rsp_valid[w_gnt_id] = s_rsp_valid && r_cmd_sent;
        end
    end

    // Response: back to the granted master; accepting it ends the grant
    assign s_rsp_ready   = w_gnt_valid && r_cmd_sent && m_rsp_ready[w_gnt_id];
    assign m_rsp_prdata  = s_rsp_prdata;
    assign m_rsp_pslverr = s_rsp_pslverr;
    assign w_ack         = (s_rsp_valid && s_rsp_ready) ? w_gnt : '0;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cmd_sent <= 1'b0;
        end else if (s_rsp_valid && s_rsp_ready) begin
            r_cmd_sent <= 1'b0;
        end else if (s_cmd_valid && s_cmd_ready) begin
            r_cmd_sent <= 1'b1;
        end
    )

endmodule : rapids_g_reg_arb
