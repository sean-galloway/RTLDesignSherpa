// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_slave_cdc
// Purpose: Apb Slave Cdc module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_slave_cdc #(
    parameter int ADDR_WIDTH  = 32,
    parameter int DATA_WIDTH  = 32,
    parameter int STRB_WIDTH  = DATA_WIDTH / 8,
    parameter int PROT_WIDTH  = 3,
    parameter int DEPTH       = 2,
    // Async-FIFO pointer encoding, surfaced here rather than left to the FIFO's
    // own default: 0 = Gray (power-of-2 DEPTH only), 1 = Johnson (any DEPTH).
    // Defaults to 0. Johnson is opt-in and must be a conscious choice -- its
    // pointers are DEPTH bits wide against Gray's $clog2(DEPTH)+1, duplicated
    // per domain and per synchronizer stage.
    parameter int USE_JOHNSON = 0,
    // DEPRECATED / NO EFFECT. The cmd+rsp CDC is now a gray-pointer async FIFO
    // (gaxi_fifo_async) rather than a toggle handshake, so there is no phase
    // variant to select. Retained so existing instantiations still elaborate.
    //
    // WHY: the 2-phase handshake encodes transfer as a TOGGLE, so if the two
    // domains are reset independently the toggle parity desynchronizes and the
    // link fabricates or drops one transfer -- permanently, since nothing
    // re-syncs it. Paired with apb_slave's FSM (which returns whatever response
    // is at the head of its skid buffer for the current command, with no
    // command/response correlation) a single phantom transfer offsets the
    // response stream by one FOREVER: every read returns the previous read's
    // data. Measured on the Nexys A7 ddr2-char board 2026-07-19 -- reading one
    // pumice CSR 8x returned the previous register's value ~3 times before
    // settling, while the non-CDC harness window was stable.
    // A gray-pointer FIFO carries no parity state, so it cannot fabricate a
    // transfer this way.
    parameter bit USE_2_PHASE_CDC = 1'b1,   // deprecated, ignored
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              aclk,
    input  logic              aresetn,
    input  logic              pclk,
    input  logic              presetn,

    // APB interface
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,

    // Command Interface
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,

    // Response Interface
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr
);

    // local signal to pass between the handshake
    logic              w_cmd_valid;
    logic              w_cmd_ready;
    logic              w_cmd_pwrite;
    logic [AW-1:0]     w_cmd_paddr;
    logic [DW-1:0]     w_cmd_pwdata;
    logic [SW-1:0]     w_cmd_pstrb;
    logic [PW-1:0]     w_cmd_pprot;


    logic              w_rsp_valid;
    logic              w_rsp_ready;
    logic [DW-1:0]     w_rsp_prdata;
    logic              w_rsp_pslverr;

    apb_slave #(
        .ADDR_WIDTH   (AW),
        .DATA_WIDTH   (DW),
        .STRB_WIDTH   (SW),
        .PROT_WIDTH   (PW),
        .DEPTH        (DEPTH)
    ) u_apb_slave(
        // Clock and Reset
        .pclk         (pclk),
        .presetn      (presetn),

        // APB interface
        .s_apb_PSEL   (s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY (s_apb_PREADY),
        .s_apb_PADDR  (s_apb_PADDR),
        .s_apb_PWRITE (s_apb_PWRITE),
        .s_apb_PWDATA (s_apb_PWDATA),
        .s_apb_PSTRB  (s_apb_PSTRB),
        .s_apb_PPROT  (s_apb_PPROT),
        .s_apb_PRDATA (s_apb_PRDATA),
        .s_apb_PSLVERR(s_apb_PSLVERR),

        // Command Interface
        .cmd_valid    (w_cmd_valid),
        .cmd_ready    (w_cmd_ready),
        .cmd_pwrite   (w_cmd_pwrite),
        .cmd_paddr    (w_cmd_paddr),
        .cmd_pwdata   (w_cmd_pwdata),
        .cmd_pstrb    (w_cmd_pstrb),
        .cmd_pprot    (w_cmd_pprot),

        // Response Interface
        .rsp_valid    (w_rsp_valid),
        .rsp_ready    (w_rsp_ready),
        .rsp_prdata   (w_rsp_prdata),
        .rsp_pslverr  (w_rsp_pslverr)
    );

    // -------------------------------------------------------------------------
    // CDC: gray-pointer async FIFOs (cmd pclk->aclk, rsp aclk->pclk).
    //
    // gaxi_fifo_async resets each domain's own pointer AND that domain's crossed
    // copy of the remote pointer from the LOCAL reset. WHILE RESET IS ASSERTED
    // that leaves the resetting side self-consistent (both pointers 0 => empty),
    // and pointers are absolute positions rather than toggle parity, so there is
    // no parity-flip hazard of the kind the previous 2-phase handshake had.
    //
    // That is NOT the same as being safe under a one-sided reset, and this
    // comment used to claim it was. The crossed copy is a LIVE
    // glitch_free_n_dff_arn (N=2), so within two clocks of deassertion it
    // re-converges on the remote pointer -- which kept advancing. The resetting
    // side then sits at its own pointer 0 against an advanced remote pointer:
    //   - write side reset alone  -> WORSE than losing the unread entries. The
    //                                READ domain's copy of the write pointer is
    //                                reset by rd_rst_n, NOT wr_rst_n (see
    //                                wr_ptr_gray_cross_inst in fifo_async.sv),
    //                                so it is not cleared -- it re-converges to
    //                                the now-zero pointer over N_FLOP_CROSS rd
    //                                clocks. Meanwhile rd_ptr still holds K.
    //                                rd_ptr != wr_ptr_sync means NOT EMPTY, and
    //                                fifo_control's count wraps (0 - K mod
    //                                2^(AW+1)), so the read side sees phantom
    //                                occupancy and pops entries that were never
    //                                written. It FABRICATES, it does not swallow.
    //   - read side reset alone   -> consumed entries are REPLAYED, and
    //                                apb_slave's positionally-paired FSM can
    //                                answer a NEW command with an OLD response.
    //                                An UNREAD entry is fine: rd_ptr is already
    //                                behind wr_ptr, so resetting it to 0 rewinds
    //                                nothing and the entry is delivered once.
    // Quiesce the bus before a one-sided reset. apb_slave's IDLE orphan-response
    // guard (pop-and-drop with a $display) mitigates but does not close this;
    // apb5_slave has no equivalent guard at all.
    //
    // This matters here because the APB side (presetn) and the register/core
    // side (aresetn) are separate reset domains -- e.g. the ddr2-char harness
    // pulses only the core-side reset on CTRL.soft_reset while the APB side
    // stays up. See docs/markdown/rtl-amba/apb/apb_slave_cdc.md, which has
    // carried the correct analysis while this comment did not.
    //
    // CDC_DEPTH is the FIFO depth; >=2, power of 2 preferred for the gray/
    // Johnson pointer encoding.
    // -------------------------------------------------------------------------
    localparam int CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH;

    gaxi_fifo_async #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_cmd_cdc_fifo (
        .axi_wr_aclk    (pclk),
        .axi_wr_aresetn (presetn),
        .axi_rd_aclk    (aclk),
        .axi_rd_aresetn (aresetn),

        .wr_valid       (w_cmd_valid),
        .wr_ready       (w_cmd_ready),
        .wr_data        ({w_cmd_pwrite, w_cmd_paddr, w_cmd_pwdata, w_cmd_pstrb, w_cmd_pprot}),

        .rd_ready       (cmd_ready),
        .rd_valid       (cmd_valid),
        .rd_data        ({cmd_pwrite, cmd_paddr, cmd_pwdata, cmd_pstrb, cmd_pprot})
    );

    gaxi_fifo_async #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_rsp_cdc_fifo (
        .axi_wr_aclk    (aclk),
        .axi_wr_aresetn (aresetn),
        .axi_rd_aclk    (pclk),
        .axi_rd_aresetn (presetn),

        .wr_valid       (rsp_valid),
        .wr_ready       (rsp_ready),
        .wr_data        ({rsp_pslverr, rsp_prdata}),

        .rd_ready       (w_rsp_ready),
        .rd_valid       (w_rsp_valid),
        .rd_data        ({w_rsp_pslverr, w_rsp_prdata})
    );

endmodule : apb_slave_cdc
