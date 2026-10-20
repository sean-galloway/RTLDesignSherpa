// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_axi_stress_mem
// Purpose: Simulation harness: axi4_master_stress on a real memory -- the
//          framework's AXI4 slave BFM with a memory model behind m_axi_*.
//
// It proves the master's mem-window contract (axi_stress_pkg f_maddr): a fill
// gives the memory known contents, then random reads and writes interleave on
// it and every read still checks, because every write carries the value a
// read of its bytes expects. The test corrupts a byte of the memory model to
// show a stale or wrong byte is caught.
//
// Struct widths are exported (o_w_*) so the Python packer can check its field
// layout against the RTL instead of trusting it.
//==============================================================================

`timescale 1ns / 1ps

module tb_axi_stress_mem
    import axi_stress_pkg::*;
#(
    parameter int IW    = 4,
    parameter int DW    = 64,
    parameter int DEPTH = 16,
    parameter int NWIN  = 2
) (
    input  logic                                   aclk,
    input  logic                                   aresetn,

    input  logic                                   go,
    input  logic                                   stop,
    input  logic [$bits(stress_mdir_cfg_t)-1:0]    cfg_mrd,
    input  logic [$bits(stress_mdir_cfg_t)-1:0]    cfg_mwr,
    input  logic [NWIN*$bits(stress_win_t)-1:0]    cfg_win_flat,   // window 0 in the LSBs
    input  logic [31:0]                            cfg_hash_seed,
    output logic [$bits(stress_mdir_sts_t)-1:0]    sts_mrd,
    output logic [$bits(stress_mdir_sts_t)-1:0]    sts_mwr,

    output logic [15:0]                            o_w_win,
    output logic [15:0]                            o_w_mcfg,
    output logic [15:0]                            o_w_msts,

    output logic [IW-1:0]     m_axi_awid,
    output logic [31:0]       m_axi_awaddr,
    output logic [7:0]        m_axi_awlen,
    output logic [2:0]        m_axi_awsize,
    output logic [1:0]        m_axi_awburst,
    output logic              m_axi_awlock,
    output logic [3:0]        m_axi_awcache,
    output logic [2:0]        m_axi_awprot,
    output logic [3:0]        m_axi_awqos,
    output logic [3:0]        m_axi_awregion,
    output logic              m_axi_awuser,
    output logic              m_axi_awvalid,
    input  logic              m_axi_awready,
    output logic [DW-1:0]     m_axi_wdata,
    output logic [DW/8-1:0]   m_axi_wstrb,
    output logic              m_axi_wlast,
    output logic              m_axi_wuser,
    output logic              m_axi_wvalid,
    input  logic              m_axi_wready,
    input  logic [IW-1:0]     m_axi_bid,
    input  logic [1:0]        m_axi_bresp,
    input  logic              m_axi_buser,
    input  logic              m_axi_bvalid,
    output logic              m_axi_bready,
    output logic [IW-1:0]     m_axi_arid,
    output logic [31:0]       m_axi_araddr,
    output logic [7:0]        m_axi_arlen,
    output logic [2:0]        m_axi_arsize,
    output logic [1:0]        m_axi_arburst,
    output logic              m_axi_arlock,
    output logic [3:0]        m_axi_arcache,
    output logic [2:0]        m_axi_arprot,
    output logic [3:0]        m_axi_arqos,
    output logic [3:0]        m_axi_arregion,
    output logic              m_axi_aruser,
    output logic              m_axi_arvalid,
    input  logic              m_axi_arready,
    input  logic [IW-1:0]     m_axi_rid,
    input  logic [DW-1:0]     m_axi_rdata,
    input  logic [1:0]        m_axi_rresp,
    input  logic              m_axi_rlast,
    input  logic              m_axi_ruser,
    input  logic              m_axi_rvalid,
    output logic              m_axi_rready
);

    assign o_w_win  = 16'($bits(stress_win_t));
    assign o_w_mcfg = 16'($bits(stress_mdir_cfg_t));
    assign o_w_msts = 16'($bits(stress_mdir_sts_t));

    stress_win_t w_win [NWIN];
    always_comb
        for (int i = 0; i < NWIN; i++)
            w_win[i] = cfg_win_flat[i*$bits(stress_win_t) +: $bits(stress_win_t)];

    stress_mdir_sts_t w_sts_mrd, w_sts_mwr;
    assign sts_mrd = w_sts_mrd;
    assign sts_mwr = w_sts_mwr;

    axi4_master_stress #(
        .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1)
    ) u_mst (
        .aclk, .aresetn, .go, .stop,
        .cfg_rd        (stress_mdir_cfg_t'(cfg_mrd)),
        .cfg_wr        (stress_mdir_cfg_t'(cfg_mwr)),
        .cfg_win       (w_win),
        .cfg_hash_seed,
        .sts_rd        (w_sts_mrd),
        .sts_wr        (w_sts_mwr),
        .m_axi_awid, .m_axi_awaddr, .m_axi_awlen, .m_axi_awsize, .m_axi_awburst,
        .m_axi_awlock, .m_axi_awcache, .m_axi_awprot, .m_axi_awqos, .m_axi_awregion,
        .m_axi_awuser, .m_axi_awvalid, .m_axi_awready,
        .m_axi_wdata, .m_axi_wstrb, .m_axi_wlast, .m_axi_wuser, .m_axi_wvalid, .m_axi_wready,
        .m_axi_bid, .m_axi_bresp, .m_axi_buser, .m_axi_bvalid, .m_axi_bready,
        .m_axi_arid, .m_axi_araddr, .m_axi_arlen, .m_axi_arsize, .m_axi_arburst,
        .m_axi_arlock, .m_axi_arcache, .m_axi_arprot, .m_axi_arqos, .m_axi_arregion,
        .m_axi_aruser, .m_axi_arvalid, .m_axi_arready,
        .m_axi_rid, .m_axi_rdata, .m_axi_rresp, .m_axi_rlast, .m_axi_ruser,
        .m_axi_rvalid, .m_axi_rready
    );

endmodule : tb_axi_stress_mem
