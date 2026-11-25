// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_axi4_arb_th
// Purpose: Test harness for peregrine_axi4_arb: unpacks the flattened
//          master-side vectors into one named AXI4 port per master
//          (s0_axi_*, s1_axi_*, s2_axi_*) so the house AXI4 BFMs bind to
//          each, and passes the fabric port (m_axi_*) through.  No logic.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24

`timescale 1ns / 1ps

module peregrine_axi4_arb_th #(
    parameter int AXI_DW = 64,
    parameter int AXI_IW = 4,
    localparam int NM    = 3,
    localparam int FIW   = AXI_IW + 2,
    localparam int STRBW = AXI_DW / 8
) (
    input  logic clk,
    input  logic rst_n,
    input  logic [AXI_IW-1:0] s0_axi_arid,
    input  logic [32-1:0] s0_axi_araddr,
    input  logic [8-1:0] s0_axi_arlen,
    input  logic [3-1:0] s0_axi_arsize,
    input  logic [2-1:0] s0_axi_arburst,
    input  logic s0_axi_arvalid,
    output logic s0_axi_arready,
    output logic [AXI_IW-1:0] s0_axi_rid,
    output logic [AXI_DW-1:0] s0_axi_rdata,
    output logic [2-1:0] s0_axi_rresp,
    output logic s0_axi_rlast,
    output logic s0_axi_rvalid,
    input  logic s0_axi_rready,
    input  logic [AXI_IW-1:0] s0_axi_awid,
    input  logic [32-1:0] s0_axi_awaddr,
    input  logic [8-1:0] s0_axi_awlen,
    input  logic [3-1:0] s0_axi_awsize,
    input  logic [2-1:0] s0_axi_awburst,
    input  logic s0_axi_awvalid,
    output logic s0_axi_awready,
    input  logic [AXI_DW-1:0] s0_axi_wdata,
    input  logic [STRBW-1:0] s0_axi_wstrb,
    input  logic s0_axi_wlast,
    input  logic s0_axi_wvalid,
    output logic s0_axi_wready,
    output logic [AXI_IW-1:0] s0_axi_bid,
    output logic [2-1:0] s0_axi_bresp,
    output logic s0_axi_bvalid,
    input  logic s0_axi_bready,
    input  logic [AXI_IW-1:0] s1_axi_arid,
    input  logic [32-1:0] s1_axi_araddr,
    input  logic [8-1:0] s1_axi_arlen,
    input  logic [3-1:0] s1_axi_arsize,
    input  logic [2-1:0] s1_axi_arburst,
    input  logic s1_axi_arvalid,
    output logic s1_axi_arready,
    output logic [AXI_IW-1:0] s1_axi_rid,
    output logic [AXI_DW-1:0] s1_axi_rdata,
    output logic [2-1:0] s1_axi_rresp,
    output logic s1_axi_rlast,
    output logic s1_axi_rvalid,
    input  logic s1_axi_rready,
    input  logic [AXI_IW-1:0] s1_axi_awid,
    input  logic [32-1:0] s1_axi_awaddr,
    input  logic [8-1:0] s1_axi_awlen,
    input  logic [3-1:0] s1_axi_awsize,
    input  logic [2-1:0] s1_axi_awburst,
    input  logic s1_axi_awvalid,
    output logic s1_axi_awready,
    input  logic [AXI_DW-1:0] s1_axi_wdata,
    input  logic [STRBW-1:0] s1_axi_wstrb,
    input  logic s1_axi_wlast,
    input  logic s1_axi_wvalid,
    output logic s1_axi_wready,
    output logic [AXI_IW-1:0] s1_axi_bid,
    output logic [2-1:0] s1_axi_bresp,
    output logic s1_axi_bvalid,
    input  logic s1_axi_bready,
    input  logic [AXI_IW-1:0] s2_axi_arid,
    input  logic [32-1:0] s2_axi_araddr,
    input  logic [8-1:0] s2_axi_arlen,
    input  logic [3-1:0] s2_axi_arsize,
    input  logic [2-1:0] s2_axi_arburst,
    input  logic s2_axi_arvalid,
    output logic s2_axi_arready,
    output logic [AXI_IW-1:0] s2_axi_rid,
    output logic [AXI_DW-1:0] s2_axi_rdata,
    output logic [2-1:0] s2_axi_rresp,
    output logic s2_axi_rlast,
    output logic s2_axi_rvalid,
    input  logic s2_axi_rready,
    input  logic [AXI_IW-1:0] s2_axi_awid,
    input  logic [32-1:0] s2_axi_awaddr,
    input  logic [8-1:0] s2_axi_awlen,
    input  logic [3-1:0] s2_axi_awsize,
    input  logic [2-1:0] s2_axi_awburst,
    input  logic s2_axi_awvalid,
    output logic s2_axi_awready,
    input  logic [AXI_DW-1:0] s2_axi_wdata,
    input  logic [STRBW-1:0] s2_axi_wstrb,
    input  logic s2_axi_wlast,
    input  logic s2_axi_wvalid,
    output logic s2_axi_wready,
    output logic [AXI_IW-1:0] s2_axi_bid,
    output logic [2-1:0] s2_axi_bresp,
    output logic s2_axi_bvalid,
    input  logic s2_axi_bready,
    output logic [FIW-1:0] m_axi_arid,
    output logic [32-1:0] m_axi_araddr,
    output logic [8-1:0] m_axi_arlen,
    output logic [3-1:0] m_axi_arsize,
    output logic [2-1:0] m_axi_arburst,
    output logic m_axi_arlock,
    output logic [4-1:0] m_axi_arcache,
    output logic [3-1:0] m_axi_arprot,
    output logic [4-1:0] m_axi_arqos,
    output logic [4-1:0] m_axi_arregion,
    output logic m_axi_arvalid,
    input  logic m_axi_arready,
    input  logic [FIW-1:0] m_axi_rid,
    input  logic [AXI_DW-1:0] m_axi_rdata,
    input  logic [2-1:0] m_axi_rresp,
    input  logic m_axi_rlast,
    input  logic m_axi_rvalid,
    output logic m_axi_rready,
    output logic [FIW-1:0] m_axi_awid,
    output logic [32-1:0] m_axi_awaddr,
    output logic [8-1:0] m_axi_awlen,
    output logic [3-1:0] m_axi_awsize,
    output logic [2-1:0] m_axi_awburst,
    output logic m_axi_awlock,
    output logic [4-1:0] m_axi_awcache,
    output logic [3-1:0] m_axi_awprot,
    output logic [4-1:0] m_axi_awqos,
    output logic [4-1:0] m_axi_awregion,
    output logic m_axi_awvalid,
    input  logic m_axi_awready,
    output logic [AXI_DW-1:0] m_axi_wdata,
    output logic [STRBW-1:0] m_axi_wstrb,
    output logic m_axi_wlast,
    output logic m_axi_wvalid,
    input  logic m_axi_wready,
    input  logic [FIW-1:0] m_axi_bid,
    input  logic [2-1:0] m_axi_bresp,
    input  logic m_axi_bvalid,
    output logic m_axi_bready
);

    logic [NM*AXI_IW-1:0] v_arid;
    logic [NM*32-1:0] v_araddr;
    logic [NM*8-1:0] v_arlen;
    logic [NM*3-1:0] v_arsize;
    logic [NM*2-1:0] v_arburst;
    logic [NM*1-1:0] v_arvalid;
    logic [NM*1-1:0] v_arready;
    logic [NM*AXI_IW-1:0] v_rid;
    logic [NM*AXI_DW-1:0] v_rdata;
    logic [NM*2-1:0] v_rresp;
    logic [NM*1-1:0] v_rlast;
    logic [NM*1-1:0] v_rvalid;
    logic [NM*1-1:0] v_rready;
    logic [NM*AXI_IW-1:0] v_awid;
    logic [NM*32-1:0] v_awaddr;
    logic [NM*8-1:0] v_awlen;
    logic [NM*3-1:0] v_awsize;
    logic [NM*2-1:0] v_awburst;
    logic [NM*1-1:0] v_awvalid;
    logic [NM*1-1:0] v_awready;
    logic [NM*AXI_DW-1:0] v_wdata;
    logic [NM*STRBW-1:0] v_wstrb;
    logic [NM*1-1:0] v_wlast;
    logic [NM*1-1:0] v_wvalid;
    logic [NM*1-1:0] v_wready;
    logic [NM*AXI_IW-1:0] v_bid;
    logic [NM*2-1:0] v_bresp;
    logic [NM*1-1:0] v_bvalid;
    logic [NM*1-1:0] v_bready;

    assign v_arid = {s2_axi_arid, s1_axi_arid, s0_axi_arid};
    assign v_araddr = {s2_axi_araddr, s1_axi_araddr, s0_axi_araddr};
    assign v_arlen = {s2_axi_arlen, s1_axi_arlen, s0_axi_arlen};
    assign v_arsize = {s2_axi_arsize, s1_axi_arsize, s0_axi_arsize};
    assign v_arburst = {s2_axi_arburst, s1_axi_arburst, s0_axi_arburst};
    assign v_arvalid = {s2_axi_arvalid, s1_axi_arvalid, s0_axi_arvalid};
    assign s0_axi_arready = v_arready[0*1 +: 1];
    assign s1_axi_arready = v_arready[1*1 +: 1];
    assign s2_axi_arready = v_arready[2*1 +: 1];
    assign s0_axi_rid = v_rid[0*AXI_IW +: AXI_IW];
    assign s1_axi_rid = v_rid[1*AXI_IW +: AXI_IW];
    assign s2_axi_rid = v_rid[2*AXI_IW +: AXI_IW];
    assign s0_axi_rdata = v_rdata[0*AXI_DW +: AXI_DW];
    assign s1_axi_rdata = v_rdata[1*AXI_DW +: AXI_DW];
    assign s2_axi_rdata = v_rdata[2*AXI_DW +: AXI_DW];
    assign s0_axi_rresp = v_rresp[0*2 +: 2];
    assign s1_axi_rresp = v_rresp[1*2 +: 2];
    assign s2_axi_rresp = v_rresp[2*2 +: 2];
    assign s0_axi_rlast = v_rlast[0*1 +: 1];
    assign s1_axi_rlast = v_rlast[1*1 +: 1];
    assign s2_axi_rlast = v_rlast[2*1 +: 1];
    assign s0_axi_rvalid = v_rvalid[0*1 +: 1];
    assign s1_axi_rvalid = v_rvalid[1*1 +: 1];
    assign s2_axi_rvalid = v_rvalid[2*1 +: 1];
    assign v_rready = {s2_axi_rready, s1_axi_rready, s0_axi_rready};
    assign v_awid = {s2_axi_awid, s1_axi_awid, s0_axi_awid};
    assign v_awaddr = {s2_axi_awaddr, s1_axi_awaddr, s0_axi_awaddr};
    assign v_awlen = {s2_axi_awlen, s1_axi_awlen, s0_axi_awlen};
    assign v_awsize = {s2_axi_awsize, s1_axi_awsize, s0_axi_awsize};
    assign v_awburst = {s2_axi_awburst, s1_axi_awburst, s0_axi_awburst};
    assign v_awvalid = {s2_axi_awvalid, s1_axi_awvalid, s0_axi_awvalid};
    assign s0_axi_awready = v_awready[0*1 +: 1];
    assign s1_axi_awready = v_awready[1*1 +: 1];
    assign s2_axi_awready = v_awready[2*1 +: 1];
    assign v_wdata = {s2_axi_wdata, s1_axi_wdata, s0_axi_wdata};
    assign v_wstrb = {s2_axi_wstrb, s1_axi_wstrb, s0_axi_wstrb};
    assign v_wlast = {s2_axi_wlast, s1_axi_wlast, s0_axi_wlast};
    assign v_wvalid = {s2_axi_wvalid, s1_axi_wvalid, s0_axi_wvalid};
    assign s0_axi_wready = v_wready[0*1 +: 1];
    assign s1_axi_wready = v_wready[1*1 +: 1];
    assign s2_axi_wready = v_wready[2*1 +: 1];
    assign s0_axi_bid = v_bid[0*AXI_IW +: AXI_IW];
    assign s1_axi_bid = v_bid[1*AXI_IW +: AXI_IW];
    assign s2_axi_bid = v_bid[2*AXI_IW +: AXI_IW];
    assign s0_axi_bresp = v_bresp[0*2 +: 2];
    assign s1_axi_bresp = v_bresp[1*2 +: 2];
    assign s2_axi_bresp = v_bresp[2*2 +: 2];
    assign s0_axi_bvalid = v_bvalid[0*1 +: 1];
    assign s1_axi_bvalid = v_bvalid[1*1 +: 1];
    assign s2_axi_bvalid = v_bvalid[2*1 +: 1];
    assign v_bready = {s2_axi_bready, s1_axi_bready, s0_axi_bready};

    peregrine_axi4_arb #(
        .NM     (NM),
        .AXI_DW (AXI_DW),
        .AXI_IW (AXI_IW)
    ) u_dut (
        .clk (clk),
        .rst_n (rst_n),
        .s_axi_arid (v_arid),
        .s_axi_araddr (v_araddr),
        .s_axi_arlen (v_arlen),
        .s_axi_arsize (v_arsize),
        .s_axi_arburst (v_arburst),
        .s_axi_arvalid (v_arvalid),
        .s_axi_arready (v_arready),
        .s_axi_rid (v_rid),
        .s_axi_rdata (v_rdata),
        .s_axi_rresp (v_rresp),
        .s_axi_rlast (v_rlast),
        .s_axi_rvalid (v_rvalid),
        .s_axi_rready (v_rready),
        .s_axi_awid (v_awid),
        .s_axi_awaddr (v_awaddr),
        .s_axi_awlen (v_awlen),
        .s_axi_awsize (v_awsize),
        .s_axi_awburst (v_awburst),
        .s_axi_awvalid (v_awvalid),
        .s_axi_awready (v_awready),
        .s_axi_wdata (v_wdata),
        .s_axi_wstrb (v_wstrb),
        .s_axi_wlast (v_wlast),
        .s_axi_wvalid (v_wvalid),
        .s_axi_wready (v_wready),
        .s_axi_bid (v_bid),
        .s_axi_bresp (v_bresp),
        .s_axi_bvalid (v_bvalid),
        .s_axi_bready (v_bready),
        .m_axi_arid (m_axi_arid),
        .m_axi_araddr (m_axi_araddr),
        .m_axi_arlen (m_axi_arlen),
        .m_axi_arsize (m_axi_arsize),
        .m_axi_arburst (m_axi_arburst),
        .m_axi_arlock (m_axi_arlock),
        .m_axi_arcache (m_axi_arcache),
        .m_axi_arprot (m_axi_arprot),
        .m_axi_arqos (m_axi_arqos),
        .m_axi_arregion (m_axi_arregion),
        .m_axi_arvalid (m_axi_arvalid),
        .m_axi_arready (m_axi_arready),
        .m_axi_rid (m_axi_rid),
        .m_axi_rdata (m_axi_rdata),
        .m_axi_rresp (m_axi_rresp),
        .m_axi_rlast (m_axi_rlast),
        .m_axi_rvalid (m_axi_rvalid),
        .m_axi_rready (m_axi_rready),
        .m_axi_awid (m_axi_awid),
        .m_axi_awaddr (m_axi_awaddr),
        .m_axi_awlen (m_axi_awlen),
        .m_axi_awsize (m_axi_awsize),
        .m_axi_awburst (m_axi_awburst),
        .m_axi_awlock (m_axi_awlock),
        .m_axi_awcache (m_axi_awcache),
        .m_axi_awprot (m_axi_awprot),
        .m_axi_awqos (m_axi_awqos),
        .m_axi_awregion (m_axi_awregion),
        .m_axi_awvalid (m_axi_awvalid),
        .m_axi_awready (m_axi_awready),
        .m_axi_wdata (m_axi_wdata),
        .m_axi_wstrb (m_axi_wstrb),
        .m_axi_wlast (m_axi_wlast),
        .m_axi_wvalid (m_axi_wvalid),
        .m_axi_wready (m_axi_wready),
        .m_axi_bid (m_axi_bid),
        .m_axi_bresp (m_axi_bresp),
        .m_axi_bvalid (m_axi_bvalid),
        .m_axi_bready (m_axi_bready)
    );

endmodule : peregrine_axi4_arb_th
