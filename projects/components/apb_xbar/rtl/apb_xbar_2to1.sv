// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_2to1
// Purpose: Apb Xbar 2To1 module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// 2-to-1 APB crossbar with address decoding and arbitration
// 2 masters to 1 slave using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0x10000000, 0x1000FFFF]

module apb_xbar_2to1 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h10000000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master 0 APB interface (from external master 0)
    input  logic                  m0_apb_PSEL,
    input  logic                  m0_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m0_apb_PADDR,
    input  logic                  m0_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m0_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m0_apb_PSTRB,
    input  logic [2:0]            m0_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m0_apb_PRDATA,
    output logic                  m0_apb_PSLVERR,
    output logic                  m0_apb_PREADY,

    // Master 1 APB interface (from external master 1)
    input  logic                  m1_apb_PSEL,
    input  logic                  m1_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m1_apb_PADDR,
    input  logic                  m1_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m1_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m1_apb_PSTRB,
    input  logic [2:0]            m1_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m1_apb_PRDATA,
    output logic                  m1_apb_PSLVERR,
    output logic                  m1_apb_PREADY,

    // Slave 0 APB interface (to external slave 0)
    output logic                  s0_apb_PSEL,
    output logic                  s0_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s0_apb_PADDR,
    output logic                  s0_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s0_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s0_apb_PSTRB,
    output logic [2:0]            s0_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s0_apb_PRDATA,
    input  logic                  s0_apb_PSLVERR,
    input  logic                  s0_apb_PREADY
);

    // Command/Response interfaces for master 0 apb_slave
    logic                  m0_cmd_valid;
    logic                  m0_cmd_ready;
    logic                  m0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m0_cmd_paddr;
    logic [DATA_WIDTH-1:0] m0_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m0_cmd_pstrb;
    logic [2:0]            m0_cmd_pprot;
    logic                  m0_rsp_valid;
    logic                  m0_rsp_ready;
    logic [DATA_WIDTH-1:0] m0_rsp_prdata;
    logic                  m0_rsp_pslverr;

    // Command/Response interfaces for master 1 apb_slave
    logic                  m1_cmd_valid;
    logic                  m1_cmd_ready;
    logic                  m1_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m1_cmd_paddr;
    logic [DATA_WIDTH-1:0] m1_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m1_cmd_pstrb;
    logic [2:0]            m1_cmd_pprot;
    logic                  m1_rsp_valid;
    logic                  m1_rsp_ready;
    logic [DATA_WIDTH-1:0] m1_rsp_prdata;
    logic                  m1_rsp_pslverr;

    // Command/Response interfaces for slave apb_masters
    logic                  s0_cmd_valid;
    logic                  s0_cmd_ready;
    logic                  s0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot;
    logic                  s0_rsp_valid;
    logic                  s0_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata;
    logic                  s0_rsp_pslverr;

    // APB Slave 0 - converts master 0 APB to cmd/rsp
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_slave_m0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (m0_apb_PSEL),
        .s_apb_PENABLE  (m0_apb_PENABLE),
        .s_apb_PREADY   (m0_apb_PREADY),
        .s_apb_PADDR    (m0_apb_PADDR),
        .s_apb_PWRITE   (m0_apb_PWRITE),
        .s_apb_PWDATA   (m0_apb_PWDATA),
        .s_apb_PSTRB    (m0_apb_PSTRB),
        .s_apb_PPROT    (m0_apb_PPROT),
        .s_apb_PRDATA   (m0_apb_PRDATA),
        .s_apb_PSLVERR  (m0_apb_PSLVERR),
        .cmd_valid      (m0_cmd_valid),
        .cmd_ready      (m0_cmd_ready),
        .cmd_pwrite     (m0_cmd_pwrite),
        .cmd_paddr      (m0_cmd_paddr),
        .cmd_pwdata     (m0_cmd_pwdata),
        .cmd_pstrb      (m0_cmd_pstrb),
        .cmd_pprot      (m0_cmd_pprot),
        .rsp_valid      (m0_rsp_valid),
        .rsp_ready      (m0_rsp_ready),
        .rsp_prdata     (m0_rsp_prdata),
        .rsp_pslverr    (m0_rsp_pslverr)
    );

    // APB Slave 1 - converts master 1 APB to cmd/rsp
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_slave_m1 (
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (m1_apb_PSEL),
        .s_apb_PENABLE  (m1_apb_PENABLE),
        .s_apb_PREADY   (m1_apb_PREADY),
        .s_apb_PADDR    (m1_apb_PADDR),
        .s_apb_PWRITE   (m1_apb_PWRITE),
        .s_apb_PWDATA   (m1_apb_PWDATA),
        .s_apb_PSTRB    (m1_apb_PSTRB),
        .s_apb_PPROT    (m1_apb_PPROT),
        .s_apb_PRDATA   (m1_apb_PRDATA),
        .s_apb_PSLVERR  (m1_apb_PSLVERR),
        .cmd_valid      (m1_cmd_valid),
        .cmd_ready      (m1_cmd_ready),
        .cmd_pwrite     (m1_cmd_pwrite),
        .cmd_paddr      (m1_cmd_paddr),
        .cmd_pwdata     (m1_cmd_pwdata),
        .cmd_pstrb      (m1_cmd_pstrb),
        .cmd_pprot      (m1_cmd_pprot),
        .rsp_valid      (m1_rsp_valid),
        .rsp_ready      (m1_rsp_ready),
        .rsp_prdata     (m1_rsp_prdata),
        .rsp_pslverr    (m1_rsp_pslverr)
    );

    // Arbitration and command routing for each slave
    // Each slave has independent round-robin arbitration between the masters
    // Uses proven arbiter_round_robin module from rtl/common/

    // Slave 0 arbitration signals
    logic [1:0] s0_arb_request;
    logic [1:0] s0_arb_grant;
    logic [1:0] s0_arb_grant_ack;

    // Build request vector for slave 0
    always_comb begin
        s0_arb_request[0] = m0_cmd_valid;
        s0_arb_request[1] = m1_cmd_valid;
    end

    // Build grant_ack vector for slave 0 (transaction complete)
    always_comb begin
        s0_arb_grant_ack[0] = s0_arb_grant[0] && s0_rsp_valid && s0_rsp_ready;
        s0_arb_grant_ack[1] = s0_arb_grant[1] && s0_rsp_valid && s0_rsp_ready;
    end

    // Round-robin arbiter for slave 0
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s0_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s0_arb_request),
        .grant_ack  (s0_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s0_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 0
    always_comb begin
        s0_cmd_valid = 1'b0;
        s0_cmd_pwrite = 1'b0;
        s0_cmd_paddr = '0;
        s0_cmd_pwdata = '0;
        s0_cmd_pstrb = '0;
        s0_cmd_pprot = '0;
        case (1'b1)
            s0_arb_grant[0]: begin
                s0_cmd_valid = m0_cmd_valid;
                s0_cmd_pwrite = m0_cmd_pwrite;
                s0_cmd_paddr = m0_cmd_paddr;
                s0_cmd_pwdata = m0_cmd_pwdata;
                s0_cmd_pstrb = m0_cmd_pstrb;
                s0_cmd_pprot = m0_cmd_pprot;
            end
            s0_arb_grant[1]: begin
                s0_cmd_valid = m1_cmd_valid;
                s0_cmd_pwrite = m1_cmd_pwrite;
                s0_cmd_paddr = m1_cmd_paddr;
                s0_cmd_pwdata = m1_cmd_pwdata;
                s0_cmd_pstrb = m1_cmd_pstrb;
                s0_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Master cmd_ready signals
    always_comb begin
        m0_cmd_ready = 1'b0;
        m0_cmd_ready = s0_arb_grant[0] && s0_cmd_ready;
    end

    always_comb begin
        m1_cmd_ready = 1'b0;
        m1_cmd_ready = s0_arb_grant[1] && s0_cmd_ready;
    end

    // Response routing from slaves to masters
    always_comb begin
        m0_rsp_valid = 1'b0;
        m0_rsp_prdata = '0;
        m0_rsp_pslverr = 1'b0;
        if (s0_arb_grant[0]) begin
            m0_rsp_valid = s0_rsp_valid;
            m0_rsp_prdata = s0_rsp_prdata;
            m0_rsp_pslverr = s0_rsp_pslverr;
        end
    end

    always_comb begin
        m1_rsp_valid = 1'b0;
        m1_rsp_prdata = '0;
        m1_rsp_pslverr = 1'b0;
        if (s0_arb_grant[1]) begin
            m1_rsp_valid = s0_rsp_valid;
            m1_rsp_prdata = s0_rsp_prdata;
            m1_rsp_pslverr = s0_rsp_pslverr;
        end
    end

    // Slave 0 rsp_ready
    always_comb begin
        s0_rsp_ready = 1'b0;
        if (s0_arb_grant[0]) s0_rsp_ready = m0_rsp_ready;
        if (s0_arb_grant[1]) s0_rsp_ready = m1_rsp_ready;
    end

    // APB Master 0 - converts cmd/rsp to slave 0 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s0_apb_PSEL),
        .m_apb_PENABLE  (s0_apb_PENABLE),
        .m_apb_PREADY   (s0_apb_PREADY),
        .m_apb_PADDR    (s0_apb_PADDR),
        .m_apb_PWRITE   (s0_apb_PWRITE),
        .m_apb_PWDATA   (s0_apb_PWDATA),
        .m_apb_PSTRB    (s0_apb_PSTRB),
        .m_apb_PPROT    (s0_apb_PPROT),
        .m_apb_PRDATA   (s0_apb_PRDATA),
        .m_apb_PSLVERR  (s0_apb_PSLVERR),
        .cmd_valid      (s0_cmd_valid),
        .cmd_ready      (s0_cmd_ready),
        .cmd_pwrite     (s0_cmd_pwrite),
        .cmd_paddr      (s0_cmd_paddr),
        .cmd_pwdata     (s0_cmd_pwdata),
        .cmd_pstrb      (s0_cmd_pstrb),
        .cmd_pprot      (s0_cmd_pprot),
        .rsp_valid      (s0_rsp_valid),
        .rsp_ready      (s0_rsp_ready),
        .rsp_prdata     (s0_rsp_prdata),
        .rsp_pslverr    (s0_rsp_pslverr)
    );

endmodule : apb_xbar_2to1
