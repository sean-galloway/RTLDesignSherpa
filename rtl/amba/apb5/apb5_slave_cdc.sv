// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave_cdc
// Purpose: APB5 Slave with Clock Domain Crossing
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes (from master)
// - PWUSER: User-defined write data attributes (from master)
// - PRUSER: User-defined read data attributes (to master)
// - PBUSER: User-defined response attributes (to master)
// - PWAKEUP: Wake-up signal (to master)
// - Optional parity support for data integrity
// - CDC handshake for crossing clock domains
//
// Documentation: docs/markdown/RTLAmba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

module apb5_slave_cdc #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int PROT_WIDTH      = 3,
    parameter int AUSER_WIDTH     = 4,
    parameter int WUSER_WIDTH     = 4,
    parameter int RUSER_WIDTH     = 4,
    parameter int BUSER_WIDTH     = 4,
    parameter int DEPTH           = 2,
    parameter bit ENABLE_PARITY   = 0,
    // CDC handshake variant: 1 = 2-phase (toggle, faster), 0 = 4-phase (level, classic)
    parameter bit USE_2_PHASE_CDC = 1'b1,   // deprecated, ignored
    // Pointer encoding for the two CDC FIFOs:
    //    0 = Gray    - cheapest pointers ($clog2(DEPTH)+1 bits), but Gray only
    //                  closes on a power-of-2 depth
    //    1 = Johnson - any depth, at DEPTH-bit pointers (more flops)
    //   -1 = AUTO (default) - Gray when the derived FIFO depth is a power of
    //                  two, Johnson otherwise. Existing power-of-2 builds keep
    //                  Gray and their flop cost unchanged; DEPTH=6 now
    //                  elaborates instead of tripping gaxi_fifo_async's
    //                  power-of-2 $error.
    parameter int USE_JOHNSON     = -1,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,
    parameter int RPW = DW + RUW + BUW + 1
) (
    // APB Clock Domain
    input  logic              pclk,
    input  logic              presetn,

    // User Clock Domain
    input  logic              aclk,
    input  logic              aresetn,

    // APB5 interface (slave side - pclk domain)
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    input  logic [AUW-1:0]    s_apb_PAUSER,
    input  logic [WUW-1:0]    s_apb_PWUSER,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,
    output logic              s_apb_PWAKEUP,
    output logic [RUW-1:0]    s_apb_PRUSER,
    output logic [BUW-1:0]    s_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    input  logic [SW-1:0]     s_apb_PWDATAPARITY,
    input  logic              s_apb_PADDRPARITY,
    input  logic              s_apb_PCTRLPARITY,
    output logic [SW-1:0]     s_apb_PRDATAPARITY,
    output logic              s_apb_PREADYPARITY,
    output logic              s_apb_PSLVERRPARITY,

    // Command Interface (aclk domain)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,
    output logic [AUW-1:0]    cmd_pauser,
    output logic [WUW-1:0]    cmd_pwuser,

    // Response Interface (aclk domain)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
    input  logic [RUW-1:0]    rsp_pruser,
    input  logic [BUW-1:0]    rsp_pbuser,

    // Wake-up control (aclk domain)
    input  logic              wakeup_request,

    // Parity error flags (pclk domain -- NOT aclk. apb5_slave drives these
    // combinationally from PSEL/PENABLE, so they are valid only during the APB
    // access phase and cross no synchronizer. Active when ENABLE_PARITY=1.)
    output logic              parity_error_wdata,
    output logic              parity_error_ctrl
);

    // Local signals in pclk domain
    logic              w_cmd_valid;
    logic              w_cmd_ready;
    logic              w_cmd_pwrite;
    logic [AW-1:0]     w_cmd_paddr;
    logic [DW-1:0]     w_cmd_pwdata;
    logic [SW-1:0]     w_cmd_pstrb;
    logic [PW-1:0]     w_cmd_pprot;
    logic [AUW-1:0]    w_cmd_pauser;
    logic [WUW-1:0]    w_cmd_pwuser;

    logic              w_rsp_valid;
    logic              w_rsp_ready;
    logic [DW-1:0]     w_rsp_prdata;
    logic              w_rsp_pslverr;
    logic [RUW-1:0]    w_rsp_pruser;
    logic [BUW-1:0]    w_rsp_pbuser;

    // Wakeup CDC (from aclk to pclk domain)
    logic              w_wakeup_request_sync;

    // Synchronize wakeup request to pclk domain
    cdc_synchronizer #(
        .WIDTH(1)
    ) u_wakeup_sync (
        .clk       (pclk),
        .rst_n     (presetn),
        .async_in  (wakeup_request),
        .sync_out  (w_wakeup_request_sync)
    );

    // Instantiate APB5 slave (pclk domain)
    apb5_slave #(
        .ADDR_WIDTH    (AW),
        .DATA_WIDTH    (DW),
        .STRB_WIDTH    (SW),
        .PROT_WIDTH    (PW),
        .AUSER_WIDTH   (AUW),
        .WUSER_WIDTH   (WUW),
        .RUSER_WIDTH   (RUW),
        .BUSER_WIDTH   (BUW),
        .DEPTH         (DEPTH),
        .ENABLE_PARITY (ENABLE_PARITY)
    ) u_apb5_slave (
        // Clock and Reset
        .pclk              (pclk),
        .presetn           (presetn),

        // APB5 interface
        .s_apb_PSEL        (s_apb_PSEL),
        .s_apb_PENABLE     (s_apb_PENABLE),
        .s_apb_PREADY      (s_apb_PREADY),
        .s_apb_PADDR       (s_apb_PADDR),
        .s_apb_PWRITE      (s_apb_PWRITE),
        .s_apb_PWDATA      (s_apb_PWDATA),
        .s_apb_PSTRB       (s_apb_PSTRB),
        .s_apb_PPROT       (s_apb_PPROT),
        .s_apb_PAUSER      (s_apb_PAUSER),
        .s_apb_PWUSER      (s_apb_PWUSER),
        .s_apb_PRDATA      (s_apb_PRDATA),
        .s_apb_PSLVERR     (s_apb_PSLVERR),
        .s_apb_PWAKEUP     (s_apb_PWAKEUP),
        .s_apb_PRUSER      (s_apb_PRUSER),
        .s_apb_PBUSER      (s_apb_PBUSER),

        // Parity signals
        .s_apb_PWDATAPARITY  (s_apb_PWDATAPARITY),
        .s_apb_PADDRPARITY   (s_apb_PADDRPARITY),
        .s_apb_PCTRLPARITY   (s_apb_PCTRLPARITY),
        .s_apb_PRDATAPARITY  (s_apb_PRDATAPARITY),
        .s_apb_PREADYPARITY  (s_apb_PREADYPARITY),
        .s_apb_PSLVERRPARITY (s_apb_PSLVERRPARITY),

        // Command Interface (to CDC)
        .cmd_valid         (w_cmd_valid),
        .cmd_ready         (w_cmd_ready),
        .cmd_pwrite        (w_cmd_pwrite),
        .cmd_paddr         (w_cmd_paddr),
        .cmd_pwdata        (w_cmd_pwdata),
        .cmd_pstrb         (w_cmd_pstrb),
        .cmd_pprot         (w_cmd_pprot),
        .cmd_pauser        (w_cmd_pauser),
        .cmd_pwuser        (w_cmd_pwuser),

        // Response Interface (from CDC)
        .rsp_valid         (w_rsp_valid),
        .rsp_ready         (w_rsp_ready),
        .rsp_prdata        (w_rsp_prdata),
        .rsp_pslverr       (w_rsp_pslverr),
        .rsp_pruser        (w_rsp_pruser),
        .rsp_pbuser        (w_rsp_pbuser),

        // Wake-up control (synchronized from aclk)
        .wakeup_request    (w_wakeup_request_sync),

        // Parity error flags (passed through)
        .parity_error_wdata(parity_error_wdata),
        .parity_error_ctrl (parity_error_ctrl)
    );

    // -------------------------------------------------------------------------
    // CDC: gray-pointer async FIFOs (cmd pclk->aclk, rsp aclk->pclk).
    //
    // gaxi_fifo_async resets each domain's own pointer AND that domain's crossed
    // copy of the remote pointer from the LOCAL reset, so a domain reset in
    // isolation leaves that side's view self-consistent (both pointers 0 =>
    // empty). Pointers are absolute positions, not toggle parity, so an
    // independent reset of one side cannot fabricate or swallow a transfer the
    // way the previous 2-phase handshake could. This matters here because the
    // APB side (presetn) and the register/core side (aresetn) are separate reset
    // domains -- e.g. the ddr2-char harness pulses only the core-side reset on
    // CTRL.soft_reset while the APB side stays up.
    //
    // CDC_FIFO_DEPTH is the FIFO depth; >=2, power of 2 preferred for the gray/
    // Johnson pointer encoding.
    // -------------------------------------------------------------------------
    localparam int CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH;

    // Gray needs a power-of-2 depth; Johnson does not. AUTO picks per depth so
    // a non-power-of-2 DEPTH is legal here rather than an elaboration error one
    // level down.
    localparam bit CDC_DEPTH_POW2   = ((CDC_FIFO_DEPTH & (CDC_FIFO_DEPTH - 1)) == 0);
    localparam int CDC_USE_JOHNSON  = (USE_JOHNSON >= 0) ? USE_JOHNSON
                                                         : (CDC_DEPTH_POW2 ? 0 : 1);

    gaxi_fifo_async #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (CDC_USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_cmd_cdc_fifo (
        .axi_wr_aclk    (pclk),
        .axi_wr_aresetn (presetn),
        .axi_rd_aclk    (aclk),
        .axi_rd_aresetn (aresetn),

        .wr_valid       (w_cmd_valid),
        .wr_ready       (w_cmd_ready),
        .wr_data        ({w_cmd_pwrite, w_cmd_pprot, w_cmd_pstrb, w_cmd_paddr, w_cmd_pwdata,
                          w_cmd_pauser, w_cmd_pwuser}),

        .rd_ready       (cmd_ready),
        .rd_valid       (cmd_valid),
        .rd_data        ({cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
                          cmd_pauser, cmd_pwuser})
    );

    gaxi_fifo_async #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (CDC_USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_rsp_cdc_fifo (
        .axi_wr_aclk    (aclk),
        .axi_wr_aresetn (aresetn),
        .axi_rd_aclk    (pclk),
        .axi_rd_aresetn (presetn),

        .wr_valid       (rsp_valid),
        .wr_ready       (rsp_ready),
        .wr_data        ({rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser}),

        .rd_ready       (w_rsp_ready),
        .rd_valid       (w_rsp_valid),
        .rd_data        ({w_rsp_pslverr, w_rsp_prdata, w_rsp_pruser, w_rsp_pbuser})
    );

endmodule : apb5_slave_cdc
