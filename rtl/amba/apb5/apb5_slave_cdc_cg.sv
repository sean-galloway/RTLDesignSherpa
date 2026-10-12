// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave_cdc_cg
// Purpose: APB5 Slave with Clock Domain Crossing and Clock Gating
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes (from master)
// - PWUSER: User-defined write data attributes (from master)
// - PRUSER: User-defined read data attributes (to master)
// - PBUSER: User-defined response attributes (to master)
// - PWAKEUP: Requester wake-up INPUT (IHI 0024E 3.7.2, Table 3-7)
// - Optional interface parity protection (IHI 0024E ch. 5: *CHK signals,
//   odd parity, one check bit per 8 payload bits)
// - CDC handshake for crossing clock domains
// - Clock gating for power reduction during idle
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_slave_cdc_cg #(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int STRB_WIDTH          = DATA_WIDTH / 8,
    parameter int PROT_WIDTH          = 3,
    parameter int AUSER_WIDTH         = 4,
    parameter int WUSER_WIDTH         = 4,
    parameter int RUSER_WIDTH         = 4,
    parameter int BUSER_WIDTH         = 4,
    parameter int DEPTH               = 2,
    // Async-FIFO pointer encoding, passed straight through to apb5_slave_cdc:
    // 0 = Gray (default, power-of-2 derived depth only), 1 = Johnson (any
    // depth), -1 = auto-select. Surfaced here so a CG instance can reach it;
    // it used to be unreachable from this level.
    parameter int USE_JOHNSON         = 0,
    parameter bit ENABLE_PARITY       = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    // CDC handshake variant: 1 = 2-phase (toggle, faster), 0 = 4-phase (level, classic)
    parameter bit USE_2_PHASE_CDC     = 1'b1,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,
    parameter int RPW = DW + RUW + BUW + 1,
    // Parity check-signal widths (IHI 0024E Table 5-1): one bit per 8 bits
    parameter int ACW  = (AW + 7) / 8,                     // PADDRCHK
    parameter int DCW  = DW / 8,                           // PWDATACHK / PRDATACHK
    parameter int AUCW = (AUW + 7) / 8,                    // PAUSERCHK
    parameter int WUCW = (WUW + 7) / 8,                    // PWUSERCHK
    parameter int RUCW = (RUW + 7) / 8,                    // PRUSERCHK
    parameter int BUCW = (BUW + 7) / 8                     // PBUSERCHK
) (
    // APB Clock Domain
    input  logic              pclk,
    input  logic              presetn,

    // User Clock Domain
    input  logic              aclk,
    input  logic              aresetn,

    // Clock gating configuration
    input  logic              cfg_cg_enable,
    input  logic [ICW-1:0]    cfg_cg_idle_count,

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
    input  logic              s_apb_PWAKEUP,
    output logic [RUW-1:0]    s_apb_PRUSER,
    output logic [BUW-1:0]    s_apb_PBUSER,

    // Interface parity check signals, IHI 0024E ch. 5 (ENABLE_PARITY=1).
    // Odd parity; passed straight through to the wrapped core.
    input  logic [ACW-1:0]     s_apb_PADDRCHK,
    input  logic               s_apb_PCTRLCHK,       // PPROT, PWRITE
    input  logic               s_apb_PSELCHK,        // PSELxCHK
    input  logic               s_apb_PENABLECHK,
    input  logic [DCW-1:0]     s_apb_PWDATACHK,
    input  logic               s_apb_PSTRBCHK,
    input  logic [AUCW-1:0]    s_apb_PAUSERCHK,
    input  logic [WUCW-1:0]    s_apb_PWUSERCHK,
    output logic [DCW-1:0]     s_apb_PRDATACHK,
    output logic               s_apb_PREADYCHK,
    output logic               s_apb_PSLVERRCHK,
    input  logic               s_apb_PWAKEUPCHK,
    output logic [RUCW-1:0]    s_apb_PRUSERCHK,
    output logic [BUCW-1:0]    s_apb_PBUSERCHK,

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


    // Parity error flags (GATED-pclk domain -- NOT aclk. apb5_slave drives
    // these combinationally from PSEL/PENABLE and they cross no
    // synchronizer, so in this wrapper they live in the gated pclk domain
    // and are valid only during an APB access phase. Active when
    // ENABLE_PARITY=1.)
    output logic              parity_error_wdata,
    output logic              parity_error_ctrl,

    // Clock gating indicator
    output logic              cg_gating,
    // Idle indicator: activity terms quiet (registered ~wakeup)
    output logic              cg_idle
);

    // Local clock gating signals
    logic r_wakeup;
    logic gated_pclk;

    // Synchronize aclk-domain signals into pclk domain for clock gating
    // Without this, cmd_valid/rsp_valid cross unsynchronized (CDC violation)
    logic r_aclk_activity_sync1, r_aclk_activity_sync2;
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_aclk_activity_sync1 <= 1'b0;
            r_aclk_activity_sync2 <= 1'b0;
        end else begin
            r_aclk_activity_sync1 <= cmd_valid || rsp_valid;
            r_aclk_activity_sync2 <= r_aclk_activity_sync1;
        end
    )

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn))
            r_wakeup <= 1'b1;
        else
            // Keep active on the Requester's PWAKEUP (IHI 0024E 3.7.2), an
            // APB transfer in progress, or aclk-domain backend activity.
            // pclk-domain signals (PWAKEUP, PSEL, PENABLE) are used directly;
            // aclk-domain signals go through the 2-FF synchronizer above.
            // Never a peer READY ([[clock-gating-activity-terms]]).
            r_wakeup <= s_apb_PWAKEUP || s_apb_PSEL || s_apb_PENABLE || r_aclk_activity_sync2;
    )

    // Instantiate clock gate controller for pclk domain
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) amba_clock_gate_ctrl (
        .clk_in              (pclk),
        .aresetn             (presetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (r_wakeup),
        .axi_valid           ('b0),
        .clk_out             (gated_pclk),
        .gating              (cg_gating),
        /* verilator lint_off PINCONNECTEMPTY */
        .idle                (cg_idle)
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Instantiate APB5 slave with CDC (uses gated pclk)
    apb5_slave_cdc #(
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .STRB_WIDTH    (STRB_WIDTH),
        .PROT_WIDTH    (PROT_WIDTH),
        .AUSER_WIDTH   (AUSER_WIDTH),
        .WUSER_WIDTH   (WUSER_WIDTH),
        .RUSER_WIDTH   (RUSER_WIDTH),
        .BUSER_WIDTH   (BUSER_WIDTH),
        .DEPTH           (DEPTH),
        .USE_JOHNSON     (USE_JOHNSON),
        .ENABLE_PARITY   (ENABLE_PARITY),
        .USE_2_PHASE_CDC (USE_2_PHASE_CDC)
    ) u_apb5_slave_cdc (
        // APB Clock Domain (gated)
        .pclk              (gated_pclk),
        .presetn           (presetn),

        // User Clock Domain
        .aclk              (aclk),
        .aresetn           (aresetn),

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
        .s_apb_PADDRCHK      (s_apb_PADDRCHK),
        .s_apb_PCTRLCHK      (s_apb_PCTRLCHK),
        .s_apb_PSELCHK       (s_apb_PSELCHK),
        .s_apb_PENABLECHK    (s_apb_PENABLECHK),
        .s_apb_PWDATACHK     (s_apb_PWDATACHK),
        .s_apb_PSTRBCHK      (s_apb_PSTRBCHK),
        .s_apb_PAUSERCHK     (s_apb_PAUSERCHK),
        .s_apb_PWUSERCHK     (s_apb_PWUSERCHK),
        .s_apb_PRDATACHK     (s_apb_PRDATACHK),
        .s_apb_PREADYCHK     (s_apb_PREADYCHK),
        .s_apb_PSLVERRCHK    (s_apb_PSLVERRCHK),
        .s_apb_PWAKEUPCHK    (s_apb_PWAKEUPCHK),
        .s_apb_PRUSERCHK     (s_apb_PRUSERCHK),
        .s_apb_PBUSERCHK     (s_apb_PBUSERCHK),

        // Command Interface
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .cmd_pauser        (cmd_pauser),
        .cmd_pwuser        (cmd_pwuser),

        // Response Interface
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .rsp_pruser        (rsp_pruser),
        .rsp_pbuser        (rsp_pbuser),

        // Wake-up control

        // Parity error flags
        .parity_error_wdata(parity_error_wdata),
        .parity_error_ctrl (parity_error_ctrl)
    );

endmodule : apb5_slave_cdc_cg
