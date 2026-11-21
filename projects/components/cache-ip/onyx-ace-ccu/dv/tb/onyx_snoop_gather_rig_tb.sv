// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_snoop_gather_rig_tb
// Purpose:
//   The snoop-gather rig for onyx (onyx TASK-001 step 1): N_CACHES snoop
//   channel sets, each the house ACE transport back to back -- an
//   axi4ace_snoop_master mover (the CCU side) feeding an axi4ace_snoop_slave
//   mover (the cache side) -- with a BFM at both ends.  The TB's
//   AXI4ACESnoopMaster BFMs drive the m<i>_ ports as onyx's fanout will,
//   and its AXI4ACESnoopSlave BFMs answer on the c<i>_ ports as jet-prime's
//   snoop side does (jet_prime_top's m_axi_ac/cr/cd port is this shape).
//   Pure wiring: no registers of its own.  Four port sets are always
//   present so the BFMs bind by flat name; ports past N_CACHES are tied off
//   and the TB does not touch them.
//
//   Why it exists before any onyx RTL: the ACE BFM (RDS-DV components/ace,
//   2026-10-05) and these movers had only been exercised one channel set at
//   a time with single-beat snoop data.  onyx gathers N responses to one
//   broadcast and the caches answer a 64-byte line in DATA_WIDTH beats; this
//   rig is where the BFM meets that shape first, and where its gaps are
//   found before they are onyx's bugs.
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/PRD.md (D4, D10)
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21
`timescale 1ns / 1ps

module onyx_snoop_gather_rig_tb #(
    parameter int N_CACHES      = 2,    // 1..4 ports live; the rest tied off
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 64,
    parameter int SKID_DEPTH_AC = 2,
    parameter int SKID_DEPTH_CR = 4,
    parameter int SKID_DEPTH_CD = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,
    // port m0: CCU side (AXI4ACESnoopMaster BFM)
    input  logic [ADDR_WIDTH-1:0]       m0_acaddr,
    input  logic [3:0]                  m0_acsnoop,
    input  logic [2:0]                  m0_acprot,
    input  logic                        m0_acvalid,
    output logic                        m0_acready,
    output logic [4:0]                  m0_crresp,
    output logic                        m0_crvalid,
    input  logic                        m0_crready,
    output logic [DATA_WIDTH-1:0]       m0_cddata,
    output logic                        m0_cdlast,
    output logic                        m0_cdvalid,
    input  logic                        m0_cdready,
    // port c0: cache side (AXI4ACESnoopSlave BFM)
    output logic [ADDR_WIDTH-1:0]       c0_acaddr,
    output logic [3:0]                  c0_acsnoop,
    output logic [2:0]                  c0_acprot,
    output logic                        c0_acvalid,
    input  logic                        c0_acready,
    input  logic [4:0]                  c0_crresp,
    input  logic                        c0_crvalid,
    output logic                        c0_crready,
    input  logic [DATA_WIDTH-1:0]       c0_cddata,
    input  logic                        c0_cdlast,
    input  logic                        c0_cdvalid,
    output logic                        c0_cdready,
    // port m1: CCU side (AXI4ACESnoopMaster BFM)
    input  logic [ADDR_WIDTH-1:0]       m1_acaddr,
    input  logic [3:0]                  m1_acsnoop,
    input  logic [2:0]                  m1_acprot,
    input  logic                        m1_acvalid,
    output logic                        m1_acready,
    output logic [4:0]                  m1_crresp,
    output logic                        m1_crvalid,
    input  logic                        m1_crready,
    output logic [DATA_WIDTH-1:0]       m1_cddata,
    output logic                        m1_cdlast,
    output logic                        m1_cdvalid,
    input  logic                        m1_cdready,
    // port c1: cache side (AXI4ACESnoopSlave BFM)
    output logic [ADDR_WIDTH-1:0]       c1_acaddr,
    output logic [3:0]                  c1_acsnoop,
    output logic [2:0]                  c1_acprot,
    output logic                        c1_acvalid,
    input  logic                        c1_acready,
    input  logic [4:0]                  c1_crresp,
    input  logic                        c1_crvalid,
    output logic                        c1_crready,
    input  logic [DATA_WIDTH-1:0]       c1_cddata,
    input  logic                        c1_cdlast,
    input  logic                        c1_cdvalid,
    output logic                        c1_cdready,
    // port m2: CCU side (AXI4ACESnoopMaster BFM)
    input  logic [ADDR_WIDTH-1:0]       m2_acaddr,
    input  logic [3:0]                  m2_acsnoop,
    input  logic [2:0]                  m2_acprot,
    input  logic                        m2_acvalid,
    output logic                        m2_acready,
    output logic [4:0]                  m2_crresp,
    output logic                        m2_crvalid,
    input  logic                        m2_crready,
    output logic [DATA_WIDTH-1:0]       m2_cddata,
    output logic                        m2_cdlast,
    output logic                        m2_cdvalid,
    input  logic                        m2_cdready,
    // port c2: cache side (AXI4ACESnoopSlave BFM)
    output logic [ADDR_WIDTH-1:0]       c2_acaddr,
    output logic [3:0]                  c2_acsnoop,
    output logic [2:0]                  c2_acprot,
    output logic                        c2_acvalid,
    input  logic                        c2_acready,
    input  logic [4:0]                  c2_crresp,
    input  logic                        c2_crvalid,
    output logic                        c2_crready,
    input  logic [DATA_WIDTH-1:0]       c2_cddata,
    input  logic                        c2_cdlast,
    input  logic                        c2_cdvalid,
    output logic                        c2_cdready,
    // port m3: CCU side (AXI4ACESnoopMaster BFM)
    input  logic [ADDR_WIDTH-1:0]       m3_acaddr,
    input  logic [3:0]                  m3_acsnoop,
    input  logic [2:0]                  m3_acprot,
    input  logic                        m3_acvalid,
    output logic                        m3_acready,
    output logic [4:0]                  m3_crresp,
    output logic                        m3_crvalid,
    input  logic                        m3_crready,
    output logic [DATA_WIDTH-1:0]       m3_cddata,
    output logic                        m3_cdlast,
    output logic                        m3_cdvalid,
    input  logic                        m3_cdready,
    // port c3: cache side (AXI4ACESnoopSlave BFM)
    output logic [ADDR_WIDTH-1:0]       c3_acaddr,
    output logic [3:0]                  c3_acsnoop,
    output logic [2:0]                  c3_acprot,
    output logic                        c3_acvalid,
    input  logic                        c3_acready,
    input  logic [4:0]                  c3_crresp,
    input  logic                        c3_crvalid,
    output logic                        c3_crready,
    input  logic [DATA_WIDTH-1:0]       c3_cddata,
    input  logic                        c3_cdlast,
    input  logic                        c3_cdvalid,
    output logic                        c3_cdready,
    // transport movers busy, one bit per live port (OR of both movers)
    output logic [3:0]                  busy
);

    // the wire between the two movers of each port (the ACE snoop channel
    // set as it would sit between onyx and a cache)
    logic [ADDR_WIDTH-1:0] w_acaddr  [4];
    logic [3:0]            w_acsnoop [4];
    logic [2:0]            w_acprot  [4];
    logic                  w_acvalid [4];
    logic                  w_acready [4];
    logic [4:0]            w_crresp  [4];
    logic                  w_crvalid [4];
    logic                  w_crready [4];
    logic [DATA_WIDTH-1:0] w_cddata  [4];
    logic                  w_cdlast  [4];
    logic                  w_cdvalid [4];
    logic                  w_cdready [4];
    logic                  w_busy_ccu   [4];
    logic                  w_busy_cache [4];

    generate
    if (N_CACHES > 0) begin : g_port0
        axi4ace_snoop_master #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_ccu (
            .aclk(aclk), .aresetn(aresetn),
            .fub_acaddr(m0_acaddr), .fub_acsnoop(m0_acsnoop), .fub_acprot(m0_acprot),
            .fub_acvalid(m0_acvalid), .fub_acready(m0_acready),
            .fub_crresp(m0_crresp), .fub_crvalid(m0_crvalid), .fub_crready(m0_crready),
            .fub_cddata(m0_cddata), .fub_cdlast(m0_cdlast), .fub_cdvalid(m0_cdvalid),
            .fub_cdready(m0_cdready),
            .m_axi_acaddr(w_acaddr[0]), .m_axi_acsnoop(w_acsnoop[0]), .m_axi_acprot(w_acprot[0]),
            .m_axi_acvalid(w_acvalid[0]), .m_axi_acready(w_acready[0]),
            .m_axi_crresp(w_crresp[0]), .m_axi_crvalid(w_crvalid[0]), .m_axi_crready(w_crready[0]),
            .m_axi_cddata(w_cddata[0]), .m_axi_cdlast(w_cdlast[0]), .m_axi_cdvalid(w_cdvalid[0]),
            .m_axi_cdready(w_cdready[0]),
            .busy(w_busy_ccu[0])
        );
        axi4ace_snoop_slave #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_cache (
            .aclk(aclk), .aresetn(aresetn),
            .m_axi_acaddr(w_acaddr[0]), .m_axi_acsnoop(w_acsnoop[0]), .m_axi_acprot(w_acprot[0]),
            .m_axi_acvalid(w_acvalid[0]), .m_axi_acready(w_acready[0]),
            .m_axi_crresp(w_crresp[0]), .m_axi_crvalid(w_crvalid[0]), .m_axi_crready(w_crready[0]),
            .m_axi_cddata(w_cddata[0]), .m_axi_cdlast(w_cdlast[0]), .m_axi_cdvalid(w_cdvalid[0]),
            .m_axi_cdready(w_cdready[0]),
            .fub_acaddr(c0_acaddr), .fub_acsnoop(c0_acsnoop), .fub_acprot(c0_acprot),
            .fub_acvalid(c0_acvalid), .fub_acready(c0_acready),
            .fub_crresp(c0_crresp), .fub_crvalid(c0_crvalid), .fub_crready(c0_crready),
            .fub_cddata(c0_cddata), .fub_cdlast(c0_cdlast), .fub_cdvalid(c0_cdvalid),
            .fub_cdready(c0_cdready),
            .busy(w_busy_cache[0])
        );
    end else begin : g_tie0
        assign m0_acready = 1'b0;
        assign m0_crresp  = 5'd0;
        assign m0_crvalid = 1'b0;
        assign m0_cddata  = '0;
        assign m0_cdlast  = 1'b0;
        assign m0_cdvalid = 1'b0;
        assign c0_acaddr  = '0;
        assign c0_acsnoop = 4'd0;
        assign c0_acprot  = 3'd0;
        assign c0_acvalid = 1'b0;
        assign c0_crready = 1'b0;
        assign c0_cdready = 1'b0;
        assign w_acaddr[0] = '0; assign w_acsnoop[0] = 4'd0; assign w_acprot[0] = 3'd0;
        assign w_acvalid[0] = 1'b0; assign w_acready[0] = 1'b0;
        assign w_crresp[0] = 5'd0; assign w_crvalid[0] = 1'b0; assign w_crready[0] = 1'b0;
        assign w_cddata[0] = '0; assign w_cdlast[0] = 1'b0; assign w_cdvalid[0] = 1'b0;
        assign w_cdready[0] = 1'b0;
        assign w_busy_ccu[0] = 1'b0; assign w_busy_cache[0] = 1'b0;
    end
    if (N_CACHES > 1) begin : g_port1
        axi4ace_snoop_master #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_ccu (
            .aclk(aclk), .aresetn(aresetn),
            .fub_acaddr(m1_acaddr), .fub_acsnoop(m1_acsnoop), .fub_acprot(m1_acprot),
            .fub_acvalid(m1_acvalid), .fub_acready(m1_acready),
            .fub_crresp(m1_crresp), .fub_crvalid(m1_crvalid), .fub_crready(m1_crready),
            .fub_cddata(m1_cddata), .fub_cdlast(m1_cdlast), .fub_cdvalid(m1_cdvalid),
            .fub_cdready(m1_cdready),
            .m_axi_acaddr(w_acaddr[1]), .m_axi_acsnoop(w_acsnoop[1]), .m_axi_acprot(w_acprot[1]),
            .m_axi_acvalid(w_acvalid[1]), .m_axi_acready(w_acready[1]),
            .m_axi_crresp(w_crresp[1]), .m_axi_crvalid(w_crvalid[1]), .m_axi_crready(w_crready[1]),
            .m_axi_cddata(w_cddata[1]), .m_axi_cdlast(w_cdlast[1]), .m_axi_cdvalid(w_cdvalid[1]),
            .m_axi_cdready(w_cdready[1]),
            .busy(w_busy_ccu[1])
        );
        axi4ace_snoop_slave #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_cache (
            .aclk(aclk), .aresetn(aresetn),
            .m_axi_acaddr(w_acaddr[1]), .m_axi_acsnoop(w_acsnoop[1]), .m_axi_acprot(w_acprot[1]),
            .m_axi_acvalid(w_acvalid[1]), .m_axi_acready(w_acready[1]),
            .m_axi_crresp(w_crresp[1]), .m_axi_crvalid(w_crvalid[1]), .m_axi_crready(w_crready[1]),
            .m_axi_cddata(w_cddata[1]), .m_axi_cdlast(w_cdlast[1]), .m_axi_cdvalid(w_cdvalid[1]),
            .m_axi_cdready(w_cdready[1]),
            .fub_acaddr(c1_acaddr), .fub_acsnoop(c1_acsnoop), .fub_acprot(c1_acprot),
            .fub_acvalid(c1_acvalid), .fub_acready(c1_acready),
            .fub_crresp(c1_crresp), .fub_crvalid(c1_crvalid), .fub_crready(c1_crready),
            .fub_cddata(c1_cddata), .fub_cdlast(c1_cdlast), .fub_cdvalid(c1_cdvalid),
            .fub_cdready(c1_cdready),
            .busy(w_busy_cache[1])
        );
    end else begin : g_tie1
        assign m1_acready = 1'b0;
        assign m1_crresp  = 5'd0;
        assign m1_crvalid = 1'b0;
        assign m1_cddata  = '0;
        assign m1_cdlast  = 1'b0;
        assign m1_cdvalid = 1'b0;
        assign c1_acaddr  = '0;
        assign c1_acsnoop = 4'd0;
        assign c1_acprot  = 3'd0;
        assign c1_acvalid = 1'b0;
        assign c1_crready = 1'b0;
        assign c1_cdready = 1'b0;
        assign w_acaddr[1] = '0; assign w_acsnoop[1] = 4'd0; assign w_acprot[1] = 3'd0;
        assign w_acvalid[1] = 1'b0; assign w_acready[1] = 1'b0;
        assign w_crresp[1] = 5'd0; assign w_crvalid[1] = 1'b0; assign w_crready[1] = 1'b0;
        assign w_cddata[1] = '0; assign w_cdlast[1] = 1'b0; assign w_cdvalid[1] = 1'b0;
        assign w_cdready[1] = 1'b0;
        assign w_busy_ccu[1] = 1'b0; assign w_busy_cache[1] = 1'b0;
    end
    if (N_CACHES > 2) begin : g_port2
        axi4ace_snoop_master #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_ccu (
            .aclk(aclk), .aresetn(aresetn),
            .fub_acaddr(m2_acaddr), .fub_acsnoop(m2_acsnoop), .fub_acprot(m2_acprot),
            .fub_acvalid(m2_acvalid), .fub_acready(m2_acready),
            .fub_crresp(m2_crresp), .fub_crvalid(m2_crvalid), .fub_crready(m2_crready),
            .fub_cddata(m2_cddata), .fub_cdlast(m2_cdlast), .fub_cdvalid(m2_cdvalid),
            .fub_cdready(m2_cdready),
            .m_axi_acaddr(w_acaddr[2]), .m_axi_acsnoop(w_acsnoop[2]), .m_axi_acprot(w_acprot[2]),
            .m_axi_acvalid(w_acvalid[2]), .m_axi_acready(w_acready[2]),
            .m_axi_crresp(w_crresp[2]), .m_axi_crvalid(w_crvalid[2]), .m_axi_crready(w_crready[2]),
            .m_axi_cddata(w_cddata[2]), .m_axi_cdlast(w_cdlast[2]), .m_axi_cdvalid(w_cdvalid[2]),
            .m_axi_cdready(w_cdready[2]),
            .busy(w_busy_ccu[2])
        );
        axi4ace_snoop_slave #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_cache (
            .aclk(aclk), .aresetn(aresetn),
            .m_axi_acaddr(w_acaddr[2]), .m_axi_acsnoop(w_acsnoop[2]), .m_axi_acprot(w_acprot[2]),
            .m_axi_acvalid(w_acvalid[2]), .m_axi_acready(w_acready[2]),
            .m_axi_crresp(w_crresp[2]), .m_axi_crvalid(w_crvalid[2]), .m_axi_crready(w_crready[2]),
            .m_axi_cddata(w_cddata[2]), .m_axi_cdlast(w_cdlast[2]), .m_axi_cdvalid(w_cdvalid[2]),
            .m_axi_cdready(w_cdready[2]),
            .fub_acaddr(c2_acaddr), .fub_acsnoop(c2_acsnoop), .fub_acprot(c2_acprot),
            .fub_acvalid(c2_acvalid), .fub_acready(c2_acready),
            .fub_crresp(c2_crresp), .fub_crvalid(c2_crvalid), .fub_crready(c2_crready),
            .fub_cddata(c2_cddata), .fub_cdlast(c2_cdlast), .fub_cdvalid(c2_cdvalid),
            .fub_cdready(c2_cdready),
            .busy(w_busy_cache[2])
        );
    end else begin : g_tie2
        assign m2_acready = 1'b0;
        assign m2_crresp  = 5'd0;
        assign m2_crvalid = 1'b0;
        assign m2_cddata  = '0;
        assign m2_cdlast  = 1'b0;
        assign m2_cdvalid = 1'b0;
        assign c2_acaddr  = '0;
        assign c2_acsnoop = 4'd0;
        assign c2_acprot  = 3'd0;
        assign c2_acvalid = 1'b0;
        assign c2_crready = 1'b0;
        assign c2_cdready = 1'b0;
        assign w_acaddr[2] = '0; assign w_acsnoop[2] = 4'd0; assign w_acprot[2] = 3'd0;
        assign w_acvalid[2] = 1'b0; assign w_acready[2] = 1'b0;
        assign w_crresp[2] = 5'd0; assign w_crvalid[2] = 1'b0; assign w_crready[2] = 1'b0;
        assign w_cddata[2] = '0; assign w_cdlast[2] = 1'b0; assign w_cdvalid[2] = 1'b0;
        assign w_cdready[2] = 1'b0;
        assign w_busy_ccu[2] = 1'b0; assign w_busy_cache[2] = 1'b0;
    end
    if (N_CACHES > 3) begin : g_port3
        axi4ace_snoop_master #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_ccu (
            .aclk(aclk), .aresetn(aresetn),
            .fub_acaddr(m3_acaddr), .fub_acsnoop(m3_acsnoop), .fub_acprot(m3_acprot),
            .fub_acvalid(m3_acvalid), .fub_acready(m3_acready),
            .fub_crresp(m3_crresp), .fub_crvalid(m3_crvalid), .fub_crready(m3_crready),
            .fub_cddata(m3_cddata), .fub_cdlast(m3_cdlast), .fub_cdvalid(m3_cdvalid),
            .fub_cdready(m3_cdready),
            .m_axi_acaddr(w_acaddr[3]), .m_axi_acsnoop(w_acsnoop[3]), .m_axi_acprot(w_acprot[3]),
            .m_axi_acvalid(w_acvalid[3]), .m_axi_acready(w_acready[3]),
            .m_axi_crresp(w_crresp[3]), .m_axi_crvalid(w_crvalid[3]), .m_axi_crready(w_crready[3]),
            .m_axi_cddata(w_cddata[3]), .m_axi_cdlast(w_cdlast[3]), .m_axi_cdvalid(w_cdvalid[3]),
            .m_axi_cdready(w_cdready[3]),
            .busy(w_busy_ccu[3])
        );
        axi4ace_snoop_slave #(
            .SKID_DEPTH_AC(SKID_DEPTH_AC), .SKID_DEPTH_CR(SKID_DEPTH_CR),
            .SKID_DEPTH_CD(SKID_DEPTH_CD), .ADDR_WIDTH(ADDR_WIDTH),
            .DATA_WIDTH(DATA_WIDTH)
        ) u_cache (
            .aclk(aclk), .aresetn(aresetn),
            .m_axi_acaddr(w_acaddr[3]), .m_axi_acsnoop(w_acsnoop[3]), .m_axi_acprot(w_acprot[3]),
            .m_axi_acvalid(w_acvalid[3]), .m_axi_acready(w_acready[3]),
            .m_axi_crresp(w_crresp[3]), .m_axi_crvalid(w_crvalid[3]), .m_axi_crready(w_crready[3]),
            .m_axi_cddata(w_cddata[3]), .m_axi_cdlast(w_cdlast[3]), .m_axi_cdvalid(w_cdvalid[3]),
            .m_axi_cdready(w_cdready[3]),
            .fub_acaddr(c3_acaddr), .fub_acsnoop(c3_acsnoop), .fub_acprot(c3_acprot),
            .fub_acvalid(c3_acvalid), .fub_acready(c3_acready),
            .fub_crresp(c3_crresp), .fub_crvalid(c3_crvalid), .fub_crready(c3_crready),
            .fub_cddata(c3_cddata), .fub_cdlast(c3_cdlast), .fub_cdvalid(c3_cdvalid),
            .fub_cdready(c3_cdready),
            .busy(w_busy_cache[3])
        );
    end else begin : g_tie3
        assign m3_acready = 1'b0;
        assign m3_crresp  = 5'd0;
        assign m3_crvalid = 1'b0;
        assign m3_cddata  = '0;
        assign m3_cdlast  = 1'b0;
        assign m3_cdvalid = 1'b0;
        assign c3_acaddr  = '0;
        assign c3_acsnoop = 4'd0;
        assign c3_acprot  = 3'd0;
        assign c3_acvalid = 1'b0;
        assign c3_crready = 1'b0;
        assign c3_cdready = 1'b0;
        assign w_acaddr[3] = '0; assign w_acsnoop[3] = 4'd0; assign w_acprot[3] = 3'd0;
        assign w_acvalid[3] = 1'b0; assign w_acready[3] = 1'b0;
        assign w_crresp[3] = 5'd0; assign w_crvalid[3] = 1'b0; assign w_crready[3] = 1'b0;
        assign w_cddata[3] = '0; assign w_cdlast[3] = 1'b0; assign w_cdvalid[3] = 1'b0;
        assign w_cdready[3] = 1'b0;
        assign w_busy_ccu[3] = 1'b0; assign w_busy_cache[3] = 1'b0;
    end
    endgenerate

    always_comb begin
        for (int k = 0; k < 4; k++) busy[k] = w_busy_ccu[k] | w_busy_cache[k];
    end

endmodule : onyx_snoop_gather_rig_tb
