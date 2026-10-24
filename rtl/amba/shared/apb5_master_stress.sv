// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_master_stress
// Purpose: APB5 bus-stress master: axi_stress_mst_rd / axi_stress_mst_wr
//          onto one APB5 requester (apb5_master).
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The APB5 shell of the stress master: apb4_master_stress on the APB5
// requester. APB5 keeps the APB4 transfer protocol; what it adds here is
// PWAKEUP, which apb5_master drives by the rules (IHI 0024E 3.7.2: from a
// flop, raised by a pending command, held until PREADY), for the stress
// slave to wait on. PAUSER / PWUSER are driven 0 and PRUSER / PBUSER ignored
// (no stress check covers USER); parity is off (as a bridge APB5 port).
//
// As apb4_master_stress: APB moves one 32-bit transfer at a
// time, reads and writes on the same bus, with no ID, so:
//
//   transfers  the cores are built LEN_MASK = 8'h00 and SIZE_FIXED: every
//              transfer is one aligned 32-bit beat.
//   one bus    a read takes the core's AR; a write takes the core's AW and
//              its W together (the write core queues W at issue, in AW order,
//              so the head W always belongs to the head AW). When both want
//              the bus they alternate. Each becomes one apb5_master command;
//              PSTRB is the W strobes on a write and 0 on a read (APB4 3.5).
//   IDs        APB answers its commands in order, so the shell keeps
//              {write, ID} of each command in a FIFO and routes every response
//              to its core under its ID: R (RLAST 1) or B. PSLVERR is SLVERR,
//              the only APB error response.
//
// DW is 32 (APB4 data is at most 32 bits; the cores need at least 32). A
// port built for one direction (EN_RD / EN_WR = 0) elaborates no core for the
// other; its status reads done with no errors.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_master_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD   = 1'b1,
    parameter bit EN_WR   = 1'b1,
    parameter int DEPTH   = 16,
    parameter int NWIN    = 8,
    parameter int IW      = 8,          // the cores' ID width (not on the bus)
    parameter int DW      = 32,         // APB5: 32
    parameter int CMD_DEPTH = 4,
    parameter int RSP_DEPTH = 4
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              go,
    input  logic              stop,
    input  stress_mdir_cfg_t cfg_rd,
    input  stress_mdir_cfg_t cfg_wr,
    input  stress_win_t      cfg_win [NWIN],
    input  logic [31:0]       cfg_hash_seed,
    output stress_mdir_sts_t sts_rd,
    output stress_mdir_sts_t sts_wr,

    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [31:0]       m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [DW/8-1:0]   m_apb_PSTRB,
    output logic [2:0]        m_apb_PPROT,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,
    output logic              m_apb_PWAKEUP
);

    localparam logic [7:0] L_LEN_MASK = 8'h00;    // one beat per transfer

`ifndef SYNTHESIS
    initial begin : param_check
        if (DW != 32)
            $fatal(1, "apb5_master_stress: DW %0d; APB5 data is 32 bits here", DW);
    end
`endif

    // ---- the cores' fub sides ------------------------------------------------
    logic [IW-1:0]   f_arid, f_awid, f_rid, f_bid;
    logic [31:0]     f_araddr, f_awaddr;
    logic [2:0]      f_arprot, f_awprot;
    logic            f_arvalid, f_arready, f_awvalid, f_awready;
    logic [DW-1:0]   f_wdata, f_rdata;
    logic [DW/8-1:0] f_wstrb;
    logic            f_wvalid, f_wready;
    logic [1:0]      f_rresp, f_bresp;
    logic            f_rvalid, f_rready, f_bvalid, f_bready;

    generate if (EN_RD) begin : g_rd
        axi_stress_mst_rd #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_artagop   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rtag      ('0),
            .cfg (cfg_rd), .cfg_win, .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_arlen     (),
            .fub_axi_arsize    (),
            .fub_axi_arburst   (),
            .fub_axi_arlock    (),
            .fub_axi_arcache   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arprot    (f_arprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_arqos     (),
            .fub_axi_arregion  (),
            .fub_axi_aruser    (),
            .fub_axi_arsb      (),
            .fub_axi_aridunq   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (1'b1),
            .fub_axi_ruser     (1'b0),
            .fub_axi_rsb       ('0),
            .fub_axi_rpoison   (1'b0),
            .fub_axi_ridunq    (1'b0),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );
    end else begin : g_no_rd
        always_comb begin
            sts_rd      = '0;
            sts_rd.done = 1'b1;
        end
        assign f_arid    = '0;
        assign f_araddr  = '0;
        assign f_arprot  = '0;
        assign f_arvalid = 1'b0;
        assign f_rready  = 1'b1;
    end endgenerate

    generate if (EN_WR) begin : g_wr
        axi_stress_mst_wr #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awtagop     (),
            .fub_axi_wtag        (),
            .fub_axi_wtagupdate  (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_btagmatch   (2'b00),
            .cfg (cfg_wr), .cfg_win, .cfg_hash_seed, .sts (sts_wr),
            .fub_axi_awid      (f_awid),
            .fub_axi_awaddr    (f_awaddr),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awlen     (),
            .fub_axi_awsize    (),
            .fub_axi_awburst   (),
            .fub_axi_awlock    (),
            .fub_axi_awcache   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awprot    (f_awprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awqos     (),
            .fub_axi_awregion  (),
            .fub_axi_awuser    (),
            .fub_axi_awsb      (),
            .fub_axi_awidunq   (),
            .fub_axi_awatop    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_wlast     (),
            .fub_axi_wid       (),          // APB has no WID
            .fub_axi_wuser     (),
            .fub_axi_wpoison   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (1'b0),
            .fub_axi_bsb       ('0),
            .fub_axi_bidunq    (1'b0),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            // No atomics on APB: the read-return path stays idle.
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_atr_ready (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_atr_valid (1'b0),
            .fub_axi_atr_id    ('0),
            .fub_axi_atr_data  ('0),
            .fub_axi_atr_resp  (2'b00),
            .fub_axi_atr_last  (1'b0),
            .fub_axi_atr_rsb   (8'd0),
            .fub_axi_atr_poison(1'b0),
            .fub_axi_atr_ridunq(1'b0)
        );
    end else begin : g_no_wr
        always_comb begin
            sts_wr      = '0;
            sts_wr.done = 1'b1;
        end
        assign f_awid    = '0;
        assign f_awaddr  = '0;
        assign f_awprot  = '0;
        assign f_awvalid = 1'b0;
        assign f_wdata   = '0;
        assign f_wstrb   = '0;
        assign f_wvalid  = 1'b0;
        assign f_bready  = 1'b1;
    end endgenerate

    // ---- one command stream ----------------------------------------------------
    logic            cmd_valid, cmd_ready, cmd_pwrite;
    logic            rsp_valid, rsp_ready, rsp_pslverr;
    logic [DW-1:0]   rsp_prdata;
    logic            tq_wr_ready, tq_rd_valid, tq_is_wr;
    logic [IW-1:0]   tq_id;

    logic w_rd_req, w_wr_req, w_grant_wr, w_cmd_hs;
    logic r_pri_wr;                         // a write has priority next time both want the bus
    assign w_rd_req   = f_arvalid;
    assign w_wr_req   = f_awvalid && f_wvalid;
    assign w_grant_wr = w_wr_req && (!w_rd_req || r_pri_wr);
    assign cmd_valid  = (w_rd_req || w_wr_req) && tq_wr_ready;
    assign cmd_pwrite = w_grant_wr;
    assign w_cmd_hs   = cmd_valid && cmd_ready;

    assign f_arready = w_cmd_hs && !w_grant_wr;
    assign f_awready = w_cmd_hs &&  w_grant_wr;
    assign f_wready  = w_cmd_hs &&  w_grant_wr;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_pri_wr <= 1'b0;
        else if (w_cmd_hs && w_rd_req && w_wr_req) r_pri_wr <= !w_grant_wr;
    )

    // {write, ID} of every command, oldest first: APB answers in order.
    gaxi_fifo_sync #(
        .REGISTERED(0), .DATA_WIDTH(IW + 1), .DEPTH(DEPTH)
    ) u_tagq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_cmd_hs),
        .wr_ready    (tq_wr_ready),
        .wr_data     ({w_grant_wr, w_grant_wr ? f_awid : f_arid}),
        .rd_ready    (rsp_valid && rsp_ready && tq_rd_valid),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (tq_rd_valid),
        .rd_data     ({tq_is_wr, tq_id})
    );

    // ---- responses back to their cores ---------------------------------------
    assign f_rvalid  = rsp_valid && tq_rd_valid && !tq_is_wr;
    assign f_rid     = tq_id;
    assign f_rdata   = rsp_prdata;
    assign f_rresp   = rsp_pslverr ? RESP_SLVERR : RESP_OKAY;
    assign f_bvalid  = rsp_valid && tq_rd_valid &&  tq_is_wr;
    assign f_bid     = tq_id;
    assign f_bresp   = rsp_pslverr ? RESP_SLVERR : RESP_OKAY;
    assign rsp_ready = tq_rd_valid && (tq_is_wr ? f_bready : f_rready);

    apb5_master #(
        .ADDR_WIDTH(32), .DATA_WIDTH(DW), .PROT_WIDTH(3),
        .AUSER_WIDTH(1), .WUSER_WIDTH(1), .RUSER_WIDTH(1), .BUSER_WIDTH(1),
        .CMD_DEPTH(CMD_DEPTH), .RSP_DEPTH(RSP_DEPTH), .ENABLE_PARITY(1'b0)
    ) u_apb (
        .pclk          (aclk),
        .presetn       (aresetn),
        .m_apb_PSEL    (m_apb_PSEL),
        .m_apb_PENABLE (m_apb_PENABLE),
        .m_apb_PADDR   (m_apb_PADDR),
        .m_apb_PWRITE  (m_apb_PWRITE),
        .m_apb_PWDATA  (m_apb_PWDATA),
        .m_apb_PSTRB   (m_apb_PSTRB),
        .m_apb_PPROT   (m_apb_PPROT),
        /* verilator lint_off PINCONNECTEMPTY */
        .m_apb_PAUSER  (),
        .m_apb_PWUSER  (),
        /* verilator lint_on PINCONNECTEMPTY */
        .m_apb_PRDATA  (m_apb_PRDATA),
        .m_apb_PSLVERR (m_apb_PSLVERR),
        .m_apb_PREADY  (m_apb_PREADY),
        .m_apb_PWAKEUP (m_apb_PWAKEUP),
        .m_apb_PRUSER  (1'b0),
        .m_apb_PBUSER  (1'b0),
        // parity off: no check signals
        /* verilator lint_off PINCONNECTEMPTY */
        .m_apb_PADDRCHK (), .m_apb_PCTRLCHK (), .m_apb_PSELCHK (), .m_apb_PENABLECHK (),
        .m_apb_PWDATACHK (), .m_apb_PSTRBCHK (), .m_apb_PAUSERCHK (), .m_apb_PWUSERCHK (),
        .m_apb_PWAKEUPCHK (),
        /* verilator lint_on PINCONNECTEMPTY */
        .m_apb_PRDATACHK ('0), .m_apb_PREADYCHK (1'b0), .m_apb_PSLVERRCHK (1'b0),
        .m_apb_PRUSERCHK ('0), .m_apb_PBUSERCHK ('0),
        .cmd_valid     (cmd_valid),
        .cmd_ready     (cmd_ready),
        .cmd_pwrite    (cmd_pwrite),
        .cmd_paddr     (w_grant_wr ? f_awaddr : f_araddr),
        .cmd_pwdata    (w_grant_wr ? f_wdata : '0),
        .cmd_pstrb     (w_grant_wr ? f_wstrb : '0),
        .cmd_pprot     (w_grant_wr ? f_awprot : f_arprot),
        .cmd_pauser    (1'b0),
        .cmd_pwuser    (1'b0),
        .rsp_valid     (rsp_valid),
        .rsp_ready     (rsp_ready),
        .rsp_prdata    (rsp_prdata),
        .rsp_pslverr   (rsp_pslverr),
        /* verilator lint_off PINCONNECTEMPTY */
        .rsp_pruser    (),
        .rsp_pbuser    (),
        .parity_error_rdata (),
        .parity_error_ctrl  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : apb5_master_stress
