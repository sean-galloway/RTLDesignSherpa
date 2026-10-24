// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave_stress
// Purpose: Wishbone B4 bus-stress slave: one Wishbone slave (wb4_slave) in
//          front of axi_stress_slv_rd / axi_stress_slv_wr.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The Wishbone B4 shell of the stress slave. wb4_slave hands over each
// accepted transfer as a command; a read goes to the read core as a one-beat
// bus-wide INCR AR on ID 0, a write to the write core as its AW and W beat
// (each taken when the core takes it; ADR is the byte address, SEL the
// strobes).
//
// Several transfers may be in flight (pipelined B4), and Wishbone terminates
// them in command order across reads and writes -- but the two cores answer
// independently. So the shell keeps the direction of every command it has
// dispatched in a FIFO, and only the core at its head may terminate: an R
// becomes ACK with DAT_R, a B becomes ACK, any non-OKAY becomes ERR. Each
// core answers its own commands in order (one ID).
//
// Every check the core makes applies: the window (S_ADDR), every selected
// byte (S_WDATA), SEL itself (S_WSTRB). The core's reorder, interleave and
// w_first options have nothing to act on. CLASSIC = 1 is B4 standard mode.
//
// DW is 32 or 64. A port built for one direction (EN_RD / EN_WR = 0) builds
// no core for it; a transfer in that direction is terminated ERR.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_slave_stress
    import axi_stress_pkg::*;
    import wb4_pkg::*;
#(
    parameter bit EN_RD   = 1'b1,
    parameter bit EN_WR   = 1'b1,
    parameter int DEPTH   = 16,         // transfers in flight
    parameter int IW      = 8,          // the cores' ID width (not on the bus)
    parameter int DW      = 32,         // 32 or 64
    parameter int CLASSIC = 0           // 1 = B4 standard (classic) cycles
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              clear,
    input  stress_sdir_cfg_t cfg_rd,
    input  stress_sdir_cfg_t cfg_wr,
    input  logic [31:0]       cfg_hash_seed,
    output stress_sdir_sts_t sts_rd,
    output stress_sdir_sts_t sts_wr,

    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [31:0]       s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [DW/8-1:0]   s_wb_SEL,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R
);

    localparam int BUS_LG2 = $clog2(DW / 8);

`ifndef SYNTHESIS
    initial begin : param_check
        if (DW != 32 && DW != 64)
            $fatal(1, "wb4_slave_stress: DW %0d; 32 or 64", DW);
    end
`endif

    // ---- the Wishbone slave ----------------------------------------------------
    logic            cmd_valid, cmd_ready, cmd_we;
    logic [31:0]     cmd_adr;
    logic [DW-1:0]   cmd_dat;
    logic [DW/8-1:0] cmd_sel;
    logic            rsp_valid, rsp_ready;
    logic [WB4_STATUS_WIDTH-1:0] rsp_status;
    logic [DW-1:0]   rsp_dat;

    wb4_slave #(
        .ADDR_WIDTH(32), .DATA_WIDTH(DW),
        .MAX_OUTSTANDING(DEPTH), .CLASSIC(CLASSIC)
    ) u_wb (
        .clk           (aclk),
        .aresetn       (aresetn),
        .s_wb_CYC      (s_wb_CYC),
        .s_wb_STB      (s_wb_STB),
        .s_wb_WE       (s_wb_WE),
        .s_wb_ADR      (s_wb_ADR),
        .s_wb_DAT_W    (s_wb_DAT_W),
        .s_wb_SEL      (s_wb_SEL),
        .s_wb_CTI      ('0),
        .s_wb_BTE      ('0),
        .s_wb_STALL    (s_wb_STALL),
        .s_wb_ACK      (s_wb_ACK),
        .s_wb_ERR      (s_wb_ERR),
        .s_wb_RTY      (s_wb_RTY),
        .s_wb_DAT_R    (s_wb_DAT_R),
        .cmd_valid     (cmd_valid),
        .cmd_ready     (cmd_ready),
        .cmd_we        (cmd_we),
        .cmd_adr       (cmd_adr),
        .cmd_dat       (cmd_dat),
        .cmd_sel       (cmd_sel),
        /* verilator lint_off PINCONNECTEMPTY */
        .cmd_cti       (),
        .cmd_bte       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rsp_valid     (rsp_valid),
        .rsp_ready     (rsp_ready),
        .rsp_status    (rsp_status),
        .rsp_dat       (rsp_dat)
    );

    // ---- dispatch: each command to its core, its direction remembered -------
    logic r_aw_done, r_w_done;              // this write's AW / W already taken
    logic f_arvalid, f_arready, f_awvalid, f_awready, f_wvalid, f_wready;
    logic f_rvalid, f_rready, f_bvalid, f_bready;
    logic [DW-1:0] f_rdata;
    logic [1:0]    f_rresp, f_bresp;
    logic dq_wr_ready, dq_rd_valid, dq_is_wr;

    logic w_pend;                           // a command waiting for its core
    assign w_pend    = cmd_valid && dq_wr_ready;
    assign f_arvalid = w_pend && !cmd_we;
    assign f_awvalid = w_pend &&  cmd_we && !r_aw_done;
    assign f_wvalid  = w_pend &&  cmd_we && !r_w_done;

    logic w_aw_now, w_w_now, w_taken;
    assign w_aw_now  = r_aw_done || (f_awvalid && f_awready);
    assign w_w_now   = r_w_done  || (f_wvalid  && f_wready);
    assign w_taken   = w_pend && (cmd_we ? (w_aw_now && w_w_now)
                                         : (f_arvalid && f_arready));
    assign cmd_ready = w_taken;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_done <= 1'b0; r_w_done <= 1'b0;
        end else if (w_taken) begin
            r_aw_done <= 1'b0; r_w_done <= 1'b0;
        end else begin
            if (f_awvalid && f_awready) r_aw_done <= 1'b1;
            if (f_wvalid  && f_wready)  r_w_done  <= 1'b1;
        end
    )

    // Direction of each dispatched command, oldest first: Wishbone terminates
    // in this order, so only the core at the head may answer.
    gaxi_fifo_sync #(
        .REGISTERED(0), .DATA_WIDTH(1), .DEPTH(DEPTH)
    ) u_dirq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_taken),
        .wr_ready    (dq_wr_ready),
        .wr_data     (cmd_we),
        .rd_ready    (rsp_valid && rsp_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (dq_rd_valid),
        .rd_data     (dq_is_wr)
    );

    assign rsp_valid  = dq_rd_valid && (dq_is_wr ? f_bvalid : f_rvalid);
    assign rsp_dat    = dq_is_wr ? '0 : f_rdata;
    assign rsp_status = ((dq_is_wr ? f_bresp : f_rresp) != RESP_OKAY) ? WB4_RSP_ERR : WB4_RSP_ACK;
    assign f_rready   = dq_rd_valid && !dq_is_wr && rsp_ready;
    assign f_bready   = dq_rd_valid &&  dq_is_wr && rsp_ready;

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
            .fub_axi_araddr    (cmd_adr),
            .fub_axi_arlen     (8'd0),
            .fub_axi_arsize    (3'(BUS_LG2)),
            .fub_axi_arburst   (BURST_INCR),
            .fub_axi_arlock    (1'b0),
            .fub_axi_arcache   (4'd0),
            .fub_axi_arprot    (3'd0),
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
        // no read core: a read is taken at once and terminated ERR
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
            .fub_axi_awaddr    (cmd_adr),
            .fub_axi_awlen     (8'd0),
            .fub_axi_awsize    (3'(BUS_LG2)),
            .fub_axi_awburst   (BURST_INCR),
            .fub_axi_awlock    (1'b0),
            .fub_axi_awcache   (4'd0),
            .fub_axi_awprot    (3'd0),
            .fub_axi_awqos     (4'd0),
            .fub_axi_awregion  (4'd0),
            .fub_axi_awuser    (1'b0),
            .fub_axi_awsb      ('0),
            .fub_axi_awidunq   (1'b0),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (cmd_dat),
            .fub_axi_wstrb     (cmd_sel),
            .fub_axi_wid       (IW'(0)),    // Wishbone has no WID
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
        // no write core: a write is taken at once and terminated ERR
        assign sts_wr    = '0;
        assign f_awready = 1'b1;
        assign f_wready  = 1'b1;
        assign f_bvalid  = 1'b1;
        assign f_bresp   = RESP_SLVERR;
    end endgenerate

endmodule : wb4_slave_stress
