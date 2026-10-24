// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_slave_stress
// Purpose: APB4 bus-stress slave: one APB4 completer (apb4_slave) in front of
//          axi_stress_slv_rd / axi_stress_slv_wr.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The APB4 shell of the stress slave. apb4_slave hands over one transfer at
// a time as a command; a read goes to the read core as a one-beat 32-bit INCR
// AR on ID 0, a write to the write core as its AW and W beat (each taken when
// the core takes it). The command is released once the core has it, and no
// other is taken until its response is back: APB holds the bus until PREADY,
// so one response is owed at most. The core's R or B becomes the APB
// response; any non-OKAY is PSLVERR.
//
// Every check the core makes applies: the window (S_ADDR), every strobed byte
// (S_WDATA), the strobes (S_WSTRB). A bridge hands an APB slave an offset into
// its window, not the fabric address; cfg offset_mode makes the core rebuild
// base | offset (axi_stress_slv_rd / _wr) before it hashes or checks. The
// core's reorder, interleave and w_first options have nothing to act on.
//
// DW is 32. A port built for one direction (EN_RD / EN_WR = 0) builds no core
// for it; a transfer in that direction is answered PSLVERR.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb4_slave_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD   = 1'b1,
    parameter bit EN_WR   = 1'b1,
    parameter int DEPTH   = 16,
    parameter int IW      = 8,          // the cores' ID width (not on the bus)
    parameter int DW      = 32          // APB4: 32
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              clear,
    input  stress_sdir_cfg_t cfg_rd,
    input  stress_sdir_cfg_t cfg_wr,
    input  logic [31:0]       cfg_hash_seed,
    output stress_sdir_sts_t sts_rd,
    output stress_sdir_sts_t sts_wr,

    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [31:0]       s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [DW/8-1:0]   s_apb_PSTRB,
    input  logic [2:0]        s_apb_PPROT,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR
);

    localparam int BUS_LG2 = $clog2(DW / 8);

`ifndef SYNTHESIS
    initial begin : param_check
        if (DW != 32)
            $fatal(1, "apb4_slave_stress: DW %0d; APB4 data is 32 bits here", DW);
    end
`endif

    // ---- the completer -------------------------------------------------------
    logic            cmd_valid, cmd_ready, cmd_pwrite;
    logic [31:0]     cmd_paddr;
    logic [DW-1:0]   cmd_pwdata;
    logic [DW/8-1:0] cmd_pstrb;
    logic [2:0]      cmd_pprot;
    logic            rsp_valid, rsp_ready, rsp_pslverr;
    logic [DW-1:0]   rsp_prdata;

    apb4_slave #(
        .ADDR_WIDTH(32), .DATA_WIDTH(DW), .PROT_WIDTH(3)
    ) u_apb (
        .pclk          (aclk),
        .presetn       (aresetn),
        .s_apb_PSEL    (s_apb_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PREADY  (s_apb_PREADY),
        .s_apb_PADDR   (s_apb_PADDR),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (s_apb_PRDATA),
        .s_apb_PSLVERR (s_apb_PSLVERR),
        .cmd_valid     (cmd_valid),
        .cmd_ready     (cmd_ready),
        .cmd_pwrite    (cmd_pwrite),
        .cmd_paddr     (cmd_paddr),
        .cmd_pwdata    (cmd_pwdata),
        .cmd_pstrb     (cmd_pstrb),
        .cmd_pprot     (cmd_pprot),
        .rsp_valid     (rsp_valid),
        .rsp_ready     (rsp_ready),
        .rsp_prdata    (rsp_prdata),
        .rsp_pslverr   (rsp_pslverr)
    );

    // ---- dispatch: one command to its core, then wait for its response ------
    logic r_owe, r_owe_wr;                  // a response is owed, and from which core
    logic r_aw_done, r_w_done;              // this write's AW / W already taken
    logic f_arvalid, f_arready, f_awvalid, f_awready, f_wvalid, f_wready;
    logic f_rvalid, f_rready, f_bvalid, f_bready;
    logic [DW-1:0] f_rdata;
    logic [1:0]    f_rresp, f_bresp;

    logic w_pend;                           // a command waiting for its core
    assign w_pend    = cmd_valid && !r_owe;
    assign f_arvalid = w_pend && !cmd_pwrite;
    assign f_awvalid = w_pend &&  cmd_pwrite && !r_aw_done;
    assign f_wvalid  = w_pend &&  cmd_pwrite && !r_w_done;

    logic w_aw_now, w_w_now, w_taken;
    assign w_aw_now = r_aw_done || (f_awvalid && f_awready);
    assign w_w_now  = r_w_done  || (f_wvalid  && f_wready);
    assign w_taken  = w_pend && (cmd_pwrite ? (w_aw_now && w_w_now)
                                            : (f_arvalid && f_arready));
    assign cmd_ready = w_taken;

    logic w_rsp_hs;
    assign rsp_valid   = r_owe && (r_owe_wr ? f_bvalid : f_rvalid);
    assign rsp_prdata  = r_owe_wr ? '0 : f_rdata;
    assign rsp_pslverr = (r_owe_wr ? f_bresp : f_rresp) != RESP_OKAY;
    assign f_rready    = r_owe && !r_owe_wr && rsp_ready;
    assign f_bready    = r_owe &&  r_owe_wr && rsp_ready;
    assign w_rsp_hs    = rsp_valid && rsp_ready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_owe <= 1'b0; r_owe_wr <= 1'b0; r_aw_done <= 1'b0; r_w_done <= 1'b0;
        end else begin
            if (w_taken) begin
                r_owe <= 1'b1; r_owe_wr <= cmd_pwrite;
                r_aw_done <= 1'b0; r_w_done <= 1'b0;
            end else begin
                if (f_awvalid && f_awready) r_aw_done <= 1'b1;
                if (f_wvalid  && f_wready)  r_w_done  <= 1'b1;
            end
            if (w_rsp_hs) r_owe <= 1'b0;
        end
    )

    // ---- the cores -----------------------------------------------------------
    generate if (EN_RD) begin : g_rd
        axi_stress_slv_rd #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1)
        ) u_core (
            .aclk, .aresetn, .clear,
            .fub_axi_artagop   (2'b00),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rtag      (),
            /* verilator lint_on PINCONNECTEMPTY */
            .cfg (cfg_rd), .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (IW'(0)),
            .fub_axi_araddr    (cmd_paddr),
            .fub_axi_arlen     (8'd0),
            .fub_axi_arsize    (3'(BUS_LG2)),
            .fub_axi_arburst   (BURST_INCR),
            .fub_axi_arlock    (1'b0),
            .fub_axi_arcache   (4'd0),
            .fub_axi_arprot    (cmd_pprot),
            .fub_axi_arqos     (4'd0),
            .fub_axi_arregion  (4'd0),
            .fub_axi_aruser    (1'b0),
            .fub_axi_arsb      ('0),
            .fub_axi_aridunq   (1'b0),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rid       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rlast     (),
            .fub_axi_ruser     (),
            .fub_axi_rsb       (),
            .fub_axi_rpoison   (),
            .fub_axi_ridunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );
    end else begin : g_no_rd
        // no read core: a read is taken at once and answered PSLVERR
        assign sts_rd    = '0;
        assign f_arready = 1'b1;
        assign f_rvalid  = 1'b1;
        assign f_rdata   = '0;
        assign f_rresp   = RESP_SLVERR;
    end endgenerate

    generate if (EN_WR) begin : g_wr
        axi_stress_slv_wr #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1)
        ) u_core (
            .aclk, .aresetn, .clear,
            .fub_axi_awtagop   (2'b00),
            .fub_axi_wtag      ('0),
            .fub_axi_wtagupdate('0),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_btagmatch (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awatop    (6'd0),
            .fub_axi_atr_ready (1'b1),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_atr_valid (),
            .fub_axi_atr_id    (),
            .fub_axi_atr_data  (),
            .fub_axi_atr_resp  (),
            .fub_axi_atr_rsb   (),
            .fub_axi_atr_poison(),
            .fub_axi_atr_ridunq(),
            /* verilator lint_on PINCONNECTEMPTY */
            .cfg (cfg_wr), .cfg_hash_seed, .sts (sts_wr),
            .fub_axi_awid      (IW'(0)),
            .fub_axi_awaddr    (cmd_paddr),
            .fub_axi_awlen     (8'd0),
            .fub_axi_awsize    (3'(BUS_LG2)),
            .fub_axi_awburst   (BURST_INCR),
            .fub_axi_awlock    (1'b0),
            .fub_axi_awcache   (4'd0),
            .fub_axi_awprot    (cmd_pprot),
            .fub_axi_awqos     (4'd0),
            .fub_axi_awregion  (4'd0),
            .fub_axi_awuser    (1'b0),
            .fub_axi_awsb      ('0),
            .fub_axi_awidunq   (1'b0),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (cmd_pwdata),
            .fub_axi_wstrb     (cmd_pstrb),
            .fub_axi_wid       (IW'(0)),    // APB has no WID
            .fub_axi_wlast     (1'b1),      // every write is one beat
            .fub_axi_wuser     (1'b0),
            .fub_axi_wpoison   (1'b0),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_bid       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bresp     (f_bresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_buser     (),
            .fub_axi_bsb       (),
            .fub_axi_bidunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready)
        );
    end else begin : g_no_wr
        // no write core: a write is taken at once and answered PSLVERR
        assign sts_wr    = '0;
        assign f_awready = 1'b1;
        assign f_wready  = 1'b1;
        assign f_bvalid  = 1'b1;
        assign f_bresp   = RESP_SLVERR;
    end endgenerate

endmodule : apb4_slave_stress
