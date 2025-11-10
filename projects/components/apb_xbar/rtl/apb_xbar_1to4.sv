// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_1to4
// Purpose: Apb Xbar 1To4 module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// 1-to-4 APB crossbar with address decoding and arbitration
// 1 master to 4 slaves using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0x10000000, 0x1000FFFF]
//   Slave 1: [0x10010000, 0x1001FFFF]
//   Slave 2: [0x10020000, 0x1002FFFF]
//   Slave 3: [0x10030000, 0x1003FFFF]

`include "reset_defs.svh"

module apb_xbar_1to4 #(
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
    input  logic                  s0_apb_PREADY,

    // Slave 1 APB interface (to external slave 1)
    output logic                  s1_apb_PSEL,
    output logic                  s1_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s1_apb_PADDR,
    output logic                  s1_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s1_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s1_apb_PSTRB,
    output logic [2:0]            s1_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s1_apb_PRDATA,
    input  logic                  s1_apb_PSLVERR,
    input  logic                  s1_apb_PREADY,

    // Slave 2 APB interface (to external slave 2)
    output logic                  s2_apb_PSEL,
    output logic                  s2_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s2_apb_PADDR,
    output logic                  s2_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s2_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s2_apb_PSTRB,
    output logic [2:0]            s2_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s2_apb_PRDATA,
    input  logic                  s2_apb_PSLVERR,
    input  logic                  s2_apb_PREADY,

    // Slave 3 APB interface (to external slave 3)
    output logic                  s3_apb_PSEL,
    output logic                  s3_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s3_apb_PADDR,
    output logic                  s3_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s3_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s3_apb_PSTRB,
    output logic [2:0]            s3_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s3_apb_PRDATA,
    input  logic                  s3_apb_PSLVERR,
    input  logic                  s3_apb_PREADY
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

    // Command/Response interfaces for slave apb_masters
    logic                  s0_cmd_valid, s1_cmd_valid, s2_cmd_valid, s3_cmd_valid;
    logic                  s0_cmd_ready, s1_cmd_ready, s2_cmd_ready, s3_cmd_ready;
    logic                  s0_cmd_pwrite, s1_cmd_pwrite, s2_cmd_pwrite, s3_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr, s1_cmd_paddr, s2_cmd_paddr, s3_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata, s1_cmd_pwdata, s2_cmd_pwdata, s3_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb, s1_cmd_pstrb, s2_cmd_pstrb, s3_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot, s1_cmd_pprot, s2_cmd_pprot, s3_cmd_pprot;
    logic                  s0_rsp_valid, s1_rsp_valid, s2_rsp_valid, s3_rsp_valid;
    logic                  s0_rsp_ready, s1_rsp_ready, s2_rsp_ready, s3_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata, s1_rsp_prdata, s2_rsp_prdata, s3_rsp_prdata;
    logic                  s0_rsp_pslverr, s1_rsp_pslverr, s2_rsp_pslverr, s3_rsp_pslverr;

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

    // Address decode for each master
    logic [1:0] m0_slave_sel;
    logic m0_addr_in_range;
    logic [1:0] r_m0_slave_sel;  // Registered for response routing

    always_comb begin
        m0_addr_in_range = (m0_cmd_paddr >= BASE_ADDR) &&
                          (m0_cmd_paddr < (BASE_ADDR + 32'h00040000));
        m0_slave_sel = m0_cmd_paddr[17:16];

    end

    // Register slave selection for each master when command accepted
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_m0_slave_sel <= 2'd0;
        end else begin
            if (m0_cmd_valid && m0_cmd_ready) begin
                r_m0_slave_sel <= m0_slave_sel;
            end
        end
    )


    // Single master - command routing based on address decode
    assign s0_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd0);
    assign s0_cmd_pwrite = m0_cmd_pwrite;
    assign s0_cmd_paddr = m0_cmd_paddr;
    assign s0_cmd_pwdata = m0_cmd_pwdata;
    assign s0_cmd_pstrb = m0_cmd_pstrb;
    assign s0_cmd_pprot = m0_cmd_pprot;

    assign s1_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd1);
    assign s1_cmd_pwrite = m0_cmd_pwrite;
    assign s1_cmd_paddr = m0_cmd_paddr;
    assign s1_cmd_pwdata = m0_cmd_pwdata;
    assign s1_cmd_pstrb = m0_cmd_pstrb;
    assign s1_cmd_pprot = m0_cmd_pprot;

    assign s2_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd2);
    assign s2_cmd_pwrite = m0_cmd_pwrite;
    assign s2_cmd_paddr = m0_cmd_paddr;
    assign s2_cmd_pwdata = m0_cmd_pwdata;
    assign s2_cmd_pstrb = m0_cmd_pstrb;
    assign s2_cmd_pprot = m0_cmd_pprot;

    assign s3_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 2'd3);
    assign s3_cmd_pwrite = m0_cmd_pwrite;
    assign s3_cmd_paddr = m0_cmd_paddr;
    assign s3_cmd_pwdata = m0_cmd_pwdata;
    assign s3_cmd_pstrb = m0_cmd_pstrb;
    assign s3_cmd_pprot = m0_cmd_pprot;

    // Master ready when selected slave is ready
    always_comb begin
        m0_cmd_ready = 1'b0;
        if (m0_cmd_valid && m0_addr_in_range) begin
            case (m0_slave_sel)
                2'd0: m0_cmd_ready = s0_cmd_ready;
                2'd1: m0_cmd_ready = s1_cmd_ready;
                2'd2: m0_cmd_ready = s2_cmd_ready;
                2'd3: m0_cmd_ready = s3_cmd_ready;
            endcase
        end
    end

    // Response routing based on registered slave selection
    always_comb begin
        m0_rsp_valid = 1'b0;
        m0_rsp_prdata = '0;
        m0_rsp_pslverr = 1'b0;
        case (r_m0_slave_sel)
            2'd0: begin
                m0_rsp_valid = s0_rsp_valid;
                m0_rsp_prdata = s0_rsp_prdata;
                m0_rsp_pslverr = s0_rsp_pslverr;
            end
            2'd1: begin
                m0_rsp_valid = s1_rsp_valid;
                m0_rsp_prdata = s1_rsp_prdata;
                m0_rsp_pslverr = s1_rsp_pslverr;
            end
            2'd2: begin
                m0_rsp_valid = s2_rsp_valid;
                m0_rsp_prdata = s2_rsp_prdata;
                m0_rsp_pslverr = s2_rsp_pslverr;
            end
            2'd3: begin
                m0_rsp_valid = s3_rsp_valid;
                m0_rsp_prdata = s3_rsp_prdata;
                m0_rsp_pslverr = s3_rsp_pslverr;
            end
        endcase
    end

    assign s0_rsp_ready = (r_m0_slave_sel == 2'd0) ? m0_rsp_ready : 1'b0;
    assign s1_rsp_ready = (r_m0_slave_sel == 2'd1) ? m0_rsp_ready : 1'b0;
    assign s2_rsp_ready = (r_m0_slave_sel == 2'd2) ? m0_rsp_ready : 1'b0;
    assign s3_rsp_ready = (r_m0_slave_sel == 2'd3) ? m0_rsp_ready : 1'b0;
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

    // APB Master 1 - converts cmd/rsp to slave 1 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s1 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s1_apb_PSEL),
        .m_apb_PENABLE  (s1_apb_PENABLE),
        .m_apb_PREADY   (s1_apb_PREADY),
        .m_apb_PADDR    (s1_apb_PADDR),
        .m_apb_PWRITE   (s1_apb_PWRITE),
        .m_apb_PWDATA   (s1_apb_PWDATA),
        .m_apb_PSTRB    (s1_apb_PSTRB),
        .m_apb_PPROT    (s1_apb_PPROT),
        .m_apb_PRDATA   (s1_apb_PRDATA),
        .m_apb_PSLVERR  (s1_apb_PSLVERR),
        .cmd_valid      (s1_cmd_valid),
        .cmd_ready      (s1_cmd_ready),
        .cmd_pwrite     (s1_cmd_pwrite),
        .cmd_paddr      (s1_cmd_paddr),
        .cmd_pwdata     (s1_cmd_pwdata),
        .cmd_pstrb      (s1_cmd_pstrb),
        .cmd_pprot      (s1_cmd_pprot),
        .rsp_valid      (s1_rsp_valid),
        .rsp_ready      (s1_rsp_ready),
        .rsp_prdata     (s1_rsp_prdata),
        .rsp_pslverr    (s1_rsp_pslverr)
    );

    // APB Master 2 - converts cmd/rsp to slave 2 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s2 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s2_apb_PSEL),
        .m_apb_PENABLE  (s2_apb_PENABLE),
        .m_apb_PREADY   (s2_apb_PREADY),
        .m_apb_PADDR    (s2_apb_PADDR),
        .m_apb_PWRITE   (s2_apb_PWRITE),
        .m_apb_PWDATA   (s2_apb_PWDATA),
        .m_apb_PSTRB    (s2_apb_PSTRB),
        .m_apb_PPROT    (s2_apb_PPROT),
        .m_apb_PRDATA   (s2_apb_PRDATA),
        .m_apb_PSLVERR  (s2_apb_PSLVERR),
        .cmd_valid      (s2_cmd_valid),
        .cmd_ready      (s2_cmd_ready),
        .cmd_pwrite     (s2_cmd_pwrite),
        .cmd_paddr      (s2_cmd_paddr),
        .cmd_pwdata     (s2_cmd_pwdata),
        .cmd_pstrb      (s2_cmd_pstrb),
        .cmd_pprot      (s2_cmd_pprot),
        .rsp_valid      (s2_rsp_valid),
        .rsp_ready      (s2_rsp_ready),
        .rsp_prdata     (s2_rsp_prdata),
        .rsp_pslverr    (s2_rsp_pslverr)
    );

    // APB Master 3 - converts cmd/rsp to slave 3 APB
    apb_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_s3 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s3_apb_PSEL),
        .m_apb_PENABLE  (s3_apb_PENABLE),
        .m_apb_PREADY   (s3_apb_PREADY),
        .m_apb_PADDR    (s3_apb_PADDR),
        .m_apb_PWRITE   (s3_apb_PWRITE),
        .m_apb_PWDATA   (s3_apb_PWDATA),
        .m_apb_PSTRB    (s3_apb_PSTRB),
        .m_apb_PPROT    (s3_apb_PPROT),
        .m_apb_PRDATA   (s3_apb_PRDATA),
        .m_apb_PSLVERR  (s3_apb_PSLVERR),
        .cmd_valid      (s3_cmd_valid),
        .cmd_ready      (s3_cmd_ready),
        .cmd_pwrite     (s3_cmd_pwrite),
        .cmd_paddr      (s3_cmd_paddr),
        .cmd_pwdata     (s3_cmd_pwdata),
        .cmd_pstrb      (s3_cmd_pstrb),
        .cmd_pprot      (s3_cmd_pprot),
        .rsp_valid      (s3_rsp_valid),
        .rsp_ready      (s3_rsp_ready),
        .rsp_prdata     (s3_rsp_prdata),
        .rsp_pslverr    (s3_rsp_pslverr)
    );

endmodule : apb_xbar_1to4
