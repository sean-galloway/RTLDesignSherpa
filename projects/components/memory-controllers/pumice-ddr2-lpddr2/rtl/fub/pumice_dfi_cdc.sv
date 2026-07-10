// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_cdc
// Purpose: THE single clock-domain crossing of the pumice controller. All
//          traffic between the controller domain (ctl_clk: AXI IFC + scheduler
//          + CAMs) and the PHY DFI domain (dfi_clk: phase-packer + PHY) crosses
//          here, and ONLY through gaxi_fifo_async (Gray-pointer) FIFOs — no
//          hand-rolled synchronizers, no open-loop bit crossings.
//
//   ctl -> phy : cmd, wrdata, init_start(token)
//   phy -> ctl : rddata, init_complete(token)
//
// Level signals (init_start / init_complete) cross as EVENT TOKENS: a rising
// edge on the source side pushes a 1-bit token; the sink pops it and sets a
// sticky latch. init is monotonic (once); leveling re-runs are future work.
// Payloads are opaque buses — the DFI top packs/unpacks {op,...}/{data,...}.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_cdc #(
    parameter int CMD_DW       = 32,   // {op,rank,bank,row,col,ap} packed
    parameter int WD_DW        = 72,   // {data,strb,last}
    parameter int RD_DW        = 66,   // {data,resp,last}
    parameter int CMD_DEPTH    = 8,    // even
    parameter int WD_DEPTH     = 16,   // even
    parameter int RD_DEPTH     = 16,   // even
    parameter int TOK_DEPTH    = 4,    // even
    parameter int N_FLOP_CROSS = 2
) (
    //=========================================================================
    // Controller domain (aclk)
    //=========================================================================
    input  logic              ctl_clk,
    input  logic              ctl_rstn,

    // cmd  ctl -> phy
    input  logic              cmd_valid_i,
    output logic              cmd_ready_o,
    input  logic [CMD_DW-1:0] cmd_data_i,
    // wrdata ctl -> phy
    input  logic              wd_valid_i,
    output logic              wd_ready_o,
    input  logic [WD_DW-1:0]  wd_data_i,
    // init start (level) ctl -> phy
    input  logic              init_start_i,
    // rddata phy -> ctl
    output logic              rd_valid_o,
    input  logic              rd_ready_i,
    output logic [RD_DW-1:0]  rd_data_o,
    // init complete (level) phy -> ctl (sticky latch)
    output logic              init_complete_o,

    //=========================================================================
    // PHY DFI domain (dfi_clk)
    //=========================================================================
    input  logic              dfi_clk,
    input  logic              dfi_rstn,

    // cmd out (phy)
    output logic              pcmd_valid_o,
    input  logic              pcmd_ready_i,
    output logic [CMD_DW-1:0] pcmd_data_o,
    // wrdata out (phy)
    output logic              pwd_valid_o,
    input  logic              pwd_ready_i,
    output logic [WD_DW-1:0]  pwd_data_o,
    // init start (level) phy (sticky latch)
    output logic              pinit_start_o,
    // rddata in (phy)
    input  logic              prd_valid_i,
    output logic              prd_ready_o,
    input  logic [RD_DW-1:0]  prd_data_i,
    // init complete (level) phy -> crosses to ctl
    input  logic              pinit_complete_i
);

    // ---- cmd : ctl -> phy ---------------------------------------------------
    gaxi_fifo_async #(
        .DATA_WIDTH(CMD_DW), .DEPTH(CMD_DEPTH), .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_cmd_fifo (
        .axi_wr_aclk(ctl_clk), .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk(dfi_clk), .axi_rd_aresetn(dfi_rstn),
        .wr_valid(cmd_valid_i), .wr_ready(cmd_ready_o), .wr_data(cmd_data_i),
        .rd_ready(pcmd_ready_i), .rd_valid(pcmd_valid_o), .rd_data(pcmd_data_o)
    );

    // ---- wrdata : ctl -> phy ------------------------------------------------
    gaxi_fifo_async #(
        .DATA_WIDTH(WD_DW), .DEPTH(WD_DEPTH), .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_wd_fifo (
        .axi_wr_aclk(ctl_clk), .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk(dfi_clk), .axi_rd_aresetn(dfi_rstn),
        .wr_valid(wd_valid_i), .wr_ready(wd_ready_o), .wr_data(wd_data_i),
        .rd_ready(pwd_ready_i), .rd_valid(pwd_valid_o), .rd_data(pwd_data_o)
    );

    // ---- rddata : phy -> ctl ------------------------------------------------
    gaxi_fifo_async #(
        .DATA_WIDTH(RD_DW), .DEPTH(RD_DEPTH), .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_rd_fifo (
        .axi_wr_aclk(dfi_clk), .axi_wr_aresetn(dfi_rstn),
        .axi_rd_aclk(ctl_clk), .axi_rd_aresetn(ctl_rstn),
        .wr_valid(prd_valid_i), .wr_ready(prd_ready_o), .wr_data(prd_data_i),
        .rd_ready(rd_ready_i), .rd_valid(rd_valid_o), .rd_data(rd_data_o)
    );

    // ---- init_start : ctl -> phy (level -> token -> sticky latch) ----------
    logic r_istart_d, w_istart_push;
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) r_istart_d <= 1'b0;
        else                         r_istart_d <= init_start_i;
    )
    assign w_istart_push = init_start_i && !r_istart_d;   // rising edge

    logic w_istok_valid;
    gaxi_fifo_async #(
        .DATA_WIDTH(1), .DEPTH(TOK_DEPTH), .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_istart_tok (
        .axi_wr_aclk(ctl_clk), .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk(dfi_clk), .axi_rd_aresetn(dfi_rstn),
        .wr_valid(w_istart_push), .wr_ready(), .wr_data(1'b1),
        .rd_ready(1'b1), .rd_valid(w_istok_valid), .rd_data()
    );
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) pinit_start_o <= 1'b0;
        else if (w_istok_valid)      pinit_start_o <= 1'b1;   // sticky
    )

    // ---- init_complete : phy -> ctl (level -> token -> sticky latch) -------
    logic r_icmp_d, w_icmp_push;
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) r_icmp_d <= 1'b0;
        else                         r_icmp_d <= pinit_complete_i;
    )
    assign w_icmp_push = pinit_complete_i && !r_icmp_d;   // rising edge

    logic w_icmptok_valid;
    gaxi_fifo_async #(
        .DATA_WIDTH(1), .DEPTH(TOK_DEPTH), .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_icmp_tok (
        .axi_wr_aclk(dfi_clk), .axi_wr_aresetn(dfi_rstn),
        .axi_rd_aclk(ctl_clk), .axi_rd_aresetn(ctl_rstn),
        .wr_valid(w_icmp_push), .wr_ready(), .wr_data(1'b1),
        .rd_ready(1'b1), .rd_valid(w_icmptok_valid), .rd_data()
    );
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) init_complete_o <= 1'b0;
        else if (w_icmptok_valid)    init_complete_o <= 1'b1;   // sticky
    )

endmodule : pumice_dfi_cdc
