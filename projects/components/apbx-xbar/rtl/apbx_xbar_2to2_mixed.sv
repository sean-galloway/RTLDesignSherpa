// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apbx_xbar_2to2_mixed
// Purpose: Apbx Xbar 2to2 Mixed module
//          Mixed-version ports (APBX-001): m0=apb4, m1=apb5; s0=apb5, s1=apb4.
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

// 2-to-2 APB crossbar with address decoding and arbitration
// 2 masters to 2 slaves using apb4_slave and apb4_master modules
//
// Address Map (same for all masters):
//   Slave 0: [0x10000000, 0x1000FFFF] (64KB)
//   Slave 1: [0x10010000, 0x1001FFFF] (64KB)

module apbx_xbar_2to2_mixed #(
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
    // APB5 sideband (master 1 is apb5)
    input  logic                  m1_apb_PAUSER,
    input  logic                  m1_apb_PWUSER,
    output logic                  m1_apb_PWAKEUP,
    output logic                  m1_apb_PRUSER,
    output logic                  m1_apb_PBUSER,

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
    // APB5 sideband (slave 0 is apb5)
    output logic                  s0_apb_PAUSER,
    output logic                  s0_apb_PWUSER,
    input  logic                  s0_apb_PWAKEUP,
    input  logic                  s0_apb_PRUSER,
    input  logic                  s0_apb_PBUSER,

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
    input  logic                  s1_apb_PREADY
);

    // Command/Response interfaces for master 0 apb4_slave
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

    // Command/Response interfaces for master 1 apb4_slave
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
    logic                  m1_cmd_pauser;
    logic                  m1_cmd_pwuser;
    logic                  m1_rsp_pruser;
    logic                  m1_rsp_pbuser;

    // Command/Response interfaces for slave apb4_masters
    logic                  s0_cmd_valid, s1_cmd_valid;
    logic                  s0_cmd_ready, s1_cmd_ready;
    logic                  s0_cmd_pwrite, s1_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr, s1_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata, s1_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb, s1_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot, s1_cmd_pprot;
    logic                  s0_rsp_valid, s1_rsp_valid;
    logic                  s0_rsp_ready, s1_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata, s1_rsp_prdata;
    logic                  s0_rsp_pslverr, s1_rsp_pslverr;
    logic                  s0_cmd_pauser;
    logic                  s0_cmd_pwuser;
    logic                  s0_rsp_pruser;
    logic                  s0_rsp_pbuser;

    // APB Slave 0 - converts master 0 APB4 to cmd/rsp
    apb4_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb4_slave_m0 (
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

    // APB Slave 1 - converts master 1 APB5 to cmd/rsp
    apb5_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3),
        .AUSER_WIDTH (1),
        .WUSER_WIDTH (1),
        .RUSER_WIDTH (1),
        .BUSER_WIDTH (1)
    ) u_apb5_slave_m1 (
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
        .rsp_pslverr    (m1_rsp_pslverr),
        .s_apb_PAUSER   (m1_apb_PAUSER),
        .s_apb_PWUSER   (m1_apb_PWUSER),
        .s_apb_PWAKEUP  (m1_apb_PWAKEUP),
        .s_apb_PRUSER   (m1_apb_PRUSER),
        .s_apb_PBUSER   (m1_apb_PBUSER),
        .cmd_pauser     (m1_cmd_pauser),
        .cmd_pwuser     (m1_cmd_pwuser),
        .rsp_pruser     (m1_rsp_pruser),
        .rsp_pbuser     (m1_rsp_pbuser),
        // parity feature unused (ENABLE_PARITY=0)
        .s_apb_PWDATAPARITY ('0),
        .s_apb_PADDRPARITY  ('0),
        .s_apb_PCTRLPARITY  ('0),
        .s_apb_PRDATAPARITY (),
        .s_apb_PREADYPARITY (),
        .s_apb_PSLVERRPARITY(),
        .parity_error_wdata (),
        .parity_error_ctrl  (),
        // wakeup handled inside the boundary IP
        .wakeup_request     ('0)
    );

    // Address decode for each master. The slave index comes from the
    // OFFSET (PADDR - BASE_ADDR), not raw PADDR bits: with raw bits a
    // BASE_ADDR whose select bits are nonzero silently rotated the
    // whole slave map relative to the documented address map. The
    // subtraction folds to constants at elaboration (BASE_ADDR is a
    // parameter), so this costs nothing.
    logic [ADDR_WIDTH-1:0] m0_cmd_offset;
    logic [0:0] m0_slave_sel;
    logic m0_addr_in_range;
    logic [0:0] r_m0_slave_sel;  // Registered for response routing
    logic [ADDR_WIDTH-1:0] m1_cmd_offset;
    logic [0:0] m1_slave_sel;
    logic m1_addr_in_range;
    logic [0:0] r_m1_slave_sel;  // Registered for response routing

    always_comb begin
        m0_cmd_offset    = m0_cmd_paddr - BASE_ADDR;
        m0_addr_in_range = (m0_cmd_paddr >= BASE_ADDR) &&
                          (m0_cmd_paddr < (BASE_ADDR + 32'h00020000));
        m0_slave_sel = m0_cmd_offset[16:16];

        m1_cmd_offset    = m1_cmd_paddr - BASE_ADDR;
        m1_addr_in_range = (m1_cmd_paddr >= BASE_ADDR) &&
                          (m1_cmd_paddr < (BASE_ADDR + 32'h00020000));
        m1_slave_sel = m1_cmd_offset[16:16];

    end

    // Register slave selection for each master when command accepted
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_m0_slave_sel <= 1'd0;
            r_m1_slave_sel <= 1'd0;
        end else begin
            if (m0_cmd_valid && m0_cmd_ready && m0_addr_in_range) begin
                r_m0_slave_sel <= m0_slave_sel;
            end
            if (m1_cmd_valid && m1_cmd_ready && m1_addr_in_range) begin
                r_m1_slave_sel <= m1_slave_sel;
            end
        end
    )

    // Arbitration and command routing for each slave
    // Each slave has independent round-robin arbitration between the masters
    // Uses proven arbiter_round_robin module from rtl/common/

    // Slave 0 arbitration signals
    logic [1:0] s0_arb_request;
    logic [1:0] s0_arb_grant;
    logic [1:0] s0_arb_grant_ack;

    // Build request vector for slave 0
    always_comb begin
        s0_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 1'd0;
        s0_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 1'd0;
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
        s0_cmd_pauser = 1'b0;
        s0_cmd_pwuser = 1'b0;
        case (1'b1)
            s0_arb_grant[0]: begin
                s0_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 1'd0);
                s0_cmd_pwrite = m0_cmd_pwrite;
                s0_cmd_paddr = m0_cmd_paddr;
                s0_cmd_pwdata = m0_cmd_pwdata;
                s0_cmd_pstrb = m0_cmd_pstrb;
                s0_cmd_pprot = m0_cmd_pprot;
            end
            s0_arb_grant[1]: begin
                s0_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 1'd0);
                s0_cmd_pwrite = m1_cmd_pwrite;
                s0_cmd_paddr = m1_cmd_paddr;
                s0_cmd_pwdata = m1_cmd_pwdata;
                s0_cmd_pstrb = m1_cmd_pstrb;
                s0_cmd_pprot = m1_cmd_pprot;
                s0_cmd_pauser = m1_cmd_pauser;
                s0_cmd_pwuser = m1_cmd_pwuser;
            end
        endcase
    end

    // Slave 1 arbitration signals
    logic [1:0] s1_arb_request;
    logic [1:0] s1_arb_grant;
    logic [1:0] s1_arb_grant_ack;

    // Build request vector for slave 1
    always_comb begin
        s1_arb_request[0] = m0_cmd_valid && m0_addr_in_range && m0_slave_sel == 1'd1;
        s1_arb_request[1] = m1_cmd_valid && m1_addr_in_range && m1_slave_sel == 1'd1;
    end

    // Build grant_ack vector for slave 1 (transaction complete)
    always_comb begin
        s1_arb_grant_ack[0] = s1_arb_grant[0] && s1_rsp_valid && s1_rsp_ready;
        s1_arb_grant_ack[1] = s1_arb_grant[1] && s1_rsp_valid && s1_rsp_ready;
    end

    // Round-robin arbiter for slave 1
    arbiter_round_robin #(
        .CLIENTS(2),
        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
    ) u_s1_arbiter (
        .clk        (pclk),
        .rst_n      (presetn),
        .block_arb  (1'b0),
        .request    (s1_arb_request),
        .grant_ack  (s1_arb_grant_ack),
        .grant_valid(),  // Not used
        .grant      (s1_arb_grant),
        .grant_id   (),  // Not used
        .last_grant ()   // Not used
    );

    // Command routing to slave 1
    always_comb begin
        s1_cmd_valid = 1'b0;
        s1_cmd_pwrite = 1'b0;
        s1_cmd_paddr = '0;
        s1_cmd_pwdata = '0;
        s1_cmd_pstrb = '0;
        s1_cmd_pprot = '0;
        case (1'b1)
            s1_arb_grant[0]: begin
                s1_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == 1'd1);
                s1_cmd_pwrite = m0_cmd_pwrite;
                s1_cmd_paddr = m0_cmd_paddr;
                s1_cmd_pwdata = m0_cmd_pwdata;
                s1_cmd_pstrb = m0_cmd_pstrb;
                s1_cmd_pprot = m0_cmd_pprot;
            end
            s1_arb_grant[1]: begin
                s1_cmd_valid = m1_cmd_valid && m1_addr_in_range && (m1_slave_sel == 1'd1);
                s1_cmd_pwrite = m1_cmd_pwrite;
                s1_cmd_paddr = m1_cmd_paddr;
                s1_cmd_pwdata = m1_cmd_pwdata;
                s1_cmd_pstrb = m1_cmd_pstrb;
                s1_cmd_pprot = m1_cmd_pprot;
            end
        endcase
    end

    // Master cmd_ready signals
    // Decode miss on master 0: complete locally with PSLVERR
    // rather than leaving cmd_ready low forever, which wedged the
    // external master in ACCESS with no error signature.
    logic r_m0_decerr_pending;
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_m0_decerr_pending <= 1'b0;
        end else begin
            if (m0_cmd_valid && m0_cmd_ready && !m0_addr_in_range) begin
                r_m0_decerr_pending <= 1'b1;
            end else if (r_m0_decerr_pending && m0_rsp_ready) begin
                r_m0_decerr_pending <= 1'b0;
            end
        end
    )

    // Decode miss on master 1: complete locally with PSLVERR
    // rather than leaving cmd_ready low forever, which wedged the
    // external master in ACCESS with no error signature.
    logic r_m1_decerr_pending;
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_m1_decerr_pending <= 1'b0;
        end else begin
            if (m1_cmd_valid && m1_cmd_ready && !m1_addr_in_range) begin
                r_m1_decerr_pending <= 1'b1;
            end else if (r_m1_decerr_pending && m1_rsp_ready) begin
                r_m1_decerr_pending <= 1'b0;
            end
        end
    )

    always_comb begin
        m0_cmd_ready = 1'b0;
        if (m0_cmd_valid) begin
            if (!m0_addr_in_range) begin
                m0_cmd_ready = !r_m0_decerr_pending;
            end else begin
                case (m0_slave_sel)
                    1'd0: m0_cmd_ready = s0_arb_grant[0] && s0_cmd_ready;
                    1'd1: m0_cmd_ready = s1_arb_grant[0] && s1_cmd_ready;
                endcase
            end
        end
    end

    always_comb begin
        m1_cmd_ready = 1'b0;
        if (m1_cmd_valid) begin
            if (!m1_addr_in_range) begin
                m1_cmd_ready = !r_m1_decerr_pending;
            end else begin
                case (m1_slave_sel)
                    1'd0: m1_cmd_ready = s0_arb_grant[1] && s0_cmd_ready;
                    1'd1: m1_cmd_ready = s1_arb_grant[1] && s1_cmd_ready;
                endcase
            end
        end
    end

    // Response routing from slaves to masters
    always_comb begin
        m0_rsp_valid = 1'b0;
        m0_rsp_prdata = '0;
        m0_rsp_pslverr = 1'b0;
        if (r_m0_decerr_pending) begin
            m0_rsp_valid = 1'b1;
            m0_rsp_pslverr = 1'b1;
        end else case (r_m0_slave_sel)
            1'd0: begin
                if (s0_arb_grant[0]) begin
                    m0_rsp_valid = s0_rsp_valid;
                    m0_rsp_prdata = s0_rsp_prdata;
                    m0_rsp_pslverr = s0_rsp_pslverr;
                end
            end
            1'd1: begin
                if (s1_arb_grant[0]) begin
                    m0_rsp_valid = s1_rsp_valid;
                    m0_rsp_prdata = s1_rsp_prdata;
                    m0_rsp_pslverr = s1_rsp_pslverr;
                end
            end
        endcase
    end

    always_comb begin
        m1_rsp_valid = 1'b0;
        m1_rsp_prdata = '0;
        m1_rsp_pslverr = 1'b0;
        m1_rsp_pruser = 1'b0;
        m1_rsp_pbuser = 1'b0;
        if (r_m1_decerr_pending) begin
            m1_rsp_valid = 1'b1;
            m1_rsp_pslverr = 1'b1;
        end else case (r_m1_slave_sel)
            1'd0: begin
                if (s0_arb_grant[1]) begin
                    m1_rsp_valid = s0_rsp_valid;
                    m1_rsp_prdata = s0_rsp_prdata;
                    m1_rsp_pslverr = s0_rsp_pslverr;
                    m1_rsp_pruser = s0_rsp_pruser;
                    m1_rsp_pbuser = s0_rsp_pbuser;
                end
            end
            1'd1: begin
                if (s1_arb_grant[1]) begin
                    m1_rsp_valid = s1_rsp_valid;
                    m1_rsp_prdata = s1_rsp_prdata;
                    m1_rsp_pslverr = s1_rsp_pslverr;
                end
            end
        endcase
    end

    // Slave 0 rsp_ready
    always_comb begin
        s0_rsp_ready = 1'b0;
        if (s0_arb_grant[0] && !r_m0_decerr_pending && r_m0_slave_sel == 1'd0) s0_rsp_ready = m0_rsp_ready;
        if (s0_arb_grant[1] && !r_m1_decerr_pending && r_m1_slave_sel == 1'd0) s0_rsp_ready = m1_rsp_ready;
    end

    // Slave 1 rsp_ready
    always_comb begin
        s1_rsp_ready = 1'b0;
        if (s1_arb_grant[0] && !r_m0_decerr_pending && r_m0_slave_sel == 1'd1) s1_rsp_ready = m0_rsp_ready;
        if (s1_arb_grant[1] && !r_m1_decerr_pending && r_m1_slave_sel == 1'd1) s1_rsp_ready = m1_rsp_ready;
    end

    // APB Master 0 - converts cmd/rsp to slave 0 APB5
    apb5_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3),
        .AUSER_WIDTH (1),
        .WUSER_WIDTH (1),
        .RUSER_WIDTH (1),
        .BUSER_WIDTH (1)
    ) u_apb5_master_s0 (
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
        .rsp_pslverr    (s0_rsp_pslverr),
        .m_apb_PAUSER   (s0_apb_PAUSER),
        .m_apb_PWUSER   (s0_apb_PWUSER),
        .m_apb_PWAKEUP  (s0_apb_PWAKEUP),
        .m_apb_PRUSER   (s0_apb_PRUSER),
        .m_apb_PBUSER   (s0_apb_PBUSER),
        .cmd_pauser     (s0_cmd_pauser),
        .cmd_pwuser     (s0_cmd_pwuser),
        .rsp_pwakeup    (),
        .rsp_pruser     (s0_rsp_pruser),
        .rsp_pbuser     (s0_rsp_pbuser),
        // parity feature unused (ENABLE_PARITY=0)
        .m_apb_PWDATAPARITY (),
        .m_apb_PADDRPARITY  (),
        .m_apb_PCTRLPARITY  (),
        .m_apb_PRDATAPARITY ('0),
        .m_apb_PREADYPARITY ('0),
        .m_apb_PSLVERRPARITY('0),
        .parity_error_rdata (),
        .parity_error_ctrl  (),
        .wakeup_pending     ()
    );

    // APB Master 1 - converts cmd/rsp to slave 1 APB4
    apb4_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb4_master_s1 (
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

endmodule : apbx_xbar_2to2_mixed
