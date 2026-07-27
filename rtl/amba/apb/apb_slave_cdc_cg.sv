// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_slave_cdc_cg
// Purpose: Apb Slave Cdc Cg module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_slave_cdc_cg #(
    parameter int ADDR_WIDTH         = 32,
    parameter int DATA_WIDTH         = 32,
    parameter int STRB_WIDTH         = DATA_WIDTH / 8,
    parameter int PROT_WIDTH         = 3,
    parameter int DEPTH              = 2,
    // Async-FIFO pointer encoding, surfaced here rather than left to the FIFO's
    // own default: 0 = Gray (power-of-2 DEPTH only), 1 = Johnson (any DEPTH).
    // Defaults to 0. Johnson is opt-in and must be a conscious choice -- its
    // pointers are DEPTH bits wide against Gray's $clog2(DEPTH)+1, duplicated
    // per domain and per synchronizer stage.
    parameter int USE_JOHNSON = 0,
    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter
    // CDC handshake variant: 1 = 2-phase (toggle, faster), 0 = 4-phase (level, classic)
    parameter bit USE_2_PHASE_CDC    = 1'b1,   // deprecated, ignored
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1,
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              aclk,
    input  logic              aresetn,
    input  logic              pclk,
    input  logic              presetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

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
    input  logic              rsp_pslverr,

    // Clock gating status
    output logic              pclk_cg_gating,
    output logic              pclk_cg_idle,
    output logic              aclk_cg_gating,
    output logic              aclk_cg_idle
);

    // Local Parameters
    localparam int APBCmdWidth = 1 + AW + DW + SW + PW;
    localparam int APBRspWidth = 1 + DW;

    // Gated clock signals
    logic gated_pclk;
    logic gated_aclk;

    // Internal signals for ready signals
    logic int_cmd_ready;
    logic int_rsp_ready_aclk;  // ACLK domain response ready
    logic int_rsp_ready_pclk;  // PCLK domain response ready
    logic int_apb_PREADY;

    // Combined valid signals for clock gating control - PCLK domain
    logic pclk_user_valid;
    logic pclk_axi_valid;

    // Combined valid signals for clock gating control - ACLK domain
    logic aclk_user_valid;
    logic aclk_axi_valid;

    // Synchronize pclk-domain s_apb_PSEL into aclk domain for clock gating
    // Without this, s_apb_PSEL crosses clock domains unsynchronized (CDC violation)
    logic r_psel_sync1, r_psel_sync2;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_psel_sync1 <= 1'b0;
            r_psel_sync2 <= 1'b0;
        end else begin
            r_psel_sync1 <= s_apb_PSEL;
            r_psel_sync2 <= r_psel_sync1;
        end
    end

    // Internal signals to pass between the handshake
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

    // Force PREADY to 0 when clock gating is active in PCLK domain
    assign s_apb_PREADY = pclk_cg_gating ? 1'b0 : int_apb_PREADY;

    // OR all PCLK domain valid signals for clock gating control
    assign pclk_user_valid = s_apb_PSEL || w_rsp_valid;
    assign pclk_axi_valid = w_cmd_valid;

    // OR all ACLK domain valid signals for clock gating control
    assign aclk_user_valid = rsp_valid;
    assign aclk_axi_valid = cmd_valid || cmd_ready || r_psel_sync2;

    // Force ready signals to 0 when clock gating is active in their respective domains
    assign w_cmd_ready = pclk_cg_gating ? 1'b0 : int_cmd_ready;
    assign rsp_ready = aclk_cg_gating ? 1'b0 : int_rsp_ready_aclk;
    assign w_rsp_ready = pclk_cg_gating ? 1'b0 : int_rsp_ready_pclk;  // Fixed - force to 0 during gating

    // Instantiate PCLK domain clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) pclk_gate_ctrl(
        .clk_in             (pclk),
        .aresetn            (presetn),
        .cfg_cg_enable      (cfg_cg_enable),
        .cfg_cg_idle_count  (cfg_cg_idle_count),
        .user_valid         (pclk_user_valid),
        .axi_valid          (pclk_axi_valid),
        .clk_out            (gated_pclk),
        .gating             (pclk_cg_gating),
        .idle               (pclk_cg_idle)
    );

    // Instantiate ACLK domain clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) aclk_gate_ctrl(
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (aclk_user_valid),
        .axi_valid           (aclk_axi_valid),
        .clk_out             (gated_aclk),
        .gating              (aclk_cg_gating),
        .idle                (aclk_cg_idle)
    );

    // Instantiate the APB slave with gated clock
    apb_slave #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DATA_WIDTH),
        .STRB_WIDTH   (STRB_WIDTH),
        .PROT_WIDTH   (PROT_WIDTH),
        .DEPTH        (DEPTH)
    ) u_apb_slave(
        // Clock and Reset
        .pclk         (gated_pclk),       // Use gated clock
        .presetn      (presetn),

        // APB interface
        .s_apb_PSEL   (s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY (int_apb_PREADY),  // Connect to internal signal
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
        .rsp_ready    (int_rsp_ready_pclk),  // Fixed - connect to internal signal
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
    //   - write side reset alone  -> unread entries are SWALLOWED
    //   - read side reset alone   -> consumed entries are REPLAYED, and
    //                                apb_slave's positionally-paired FSM can
    //                                answer a NEW command with an OLD response
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
    // Both sides run on the GATED clocks, matching the handshake this replaces:
    // the FIFO pointers advance only when the respective domain is clocked, so
    // gating cannot reorder or drop a queued transfer.
    //
    // CDC_FIFO_DEPTH is the FIFO depth; >=2, power of 2 preferred for the gray/
    // Johnson pointer encoding.
    // -------------------------------------------------------------------------
    localparam int CDC_FIFO_DEPTH = (DEPTH < 4) ? 4 : DEPTH;

    gaxi_fifo_async #(
        .DATA_WIDTH   (APBCmdWidth),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_cmd_cdc_fifo (
        .axi_wr_aclk    (gated_pclk),       // Use gated clock
        .axi_wr_aresetn (presetn),
        .axi_rd_aclk    (gated_aclk),       // Use gated clock
        .axi_rd_aresetn (aresetn),

        .wr_valid       (w_cmd_valid),
        .wr_ready       (int_cmd_ready),
        .wr_data        ({w_cmd_pwrite, w_cmd_paddr, w_cmd_pwdata, w_cmd_pstrb, w_cmd_pprot}),

        .rd_ready       (cmd_ready),
        .rd_valid       (cmd_valid),
        .rd_data        ({cmd_pwrite, cmd_paddr, cmd_pwdata, cmd_pstrb, cmd_pprot})
    );

    gaxi_fifo_async #(
        .DATA_WIDTH   (APBRspWidth),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_rsp_cdc_fifo (
        .axi_wr_aclk    (gated_aclk),       // Use gated clock
        .axi_wr_aresetn (aresetn),
        .axi_rd_aclk    (gated_pclk),       // Use gated clock
        .axi_rd_aresetn (presetn),

        .wr_valid       (rsp_valid),
        .wr_ready       (int_rsp_ready_aclk),
        .wr_data        ({rsp_pslverr, rsp_prdata}),

        .rd_ready       (w_rsp_ready),
        .rd_valid       (w_rsp_valid),
        .rd_data        ({w_rsp_pslverr, w_rsp_prdata})
    );

endmodule : apb_slave_cdc_cg
