// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axi4_axi4
// Purpose: AXI4 write + AXI4 read shape of sdpram_slave. Exposes only
//          AXI4 ports (s_axi_aw*/w*/b*/ar*/r* with the full AXI4 field
//          set). One of the four protocol permutations:
//            sdpram_slave_axi4_axi4    -- AXI4 wr,  AXI4 rd
//            sdpram_slave_axi4_axil    -- AXI4 wr,  AXIL rd
//            sdpram_slave_axil_axi4    -- AXIL wr,  AXI4 rd
//            sdpram_slave_axil_axil    -- AXIL wr,  AXIL rd
//
//          All four are thin shims around the common backend
//          `sdpram_slave.sv`, which owns the BRAM glue, clear FSM, and
//          protocol-skid generate blocks. SystemVerilog has no way to
//          conditionally include/exclude module ports at elaboration,
//          so the four files give each protocol combination its own
//          exact port shape.
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-06-09

`timescale 1ns / 1ps

module sdpram_slave_axi4_axi4 #(
    parameter int    AXI_ID_WIDTH = 8,
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    USER_WIDTH   = 1,
    parameter int    MEM_DEPTH    = 2048,
    parameter int    SKID_DEPTH_AW = 2,
    parameter int    SKID_DEPTH_W  = 2,
    parameter int    SKID_DEPTH_B  = 2,
    parameter int    SKID_DEPTH_AR = 2,
    parameter int    SKID_DEPTH_R  = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // ---------------------------------------------------------------
    // AXI4 slave write channels (AW + W + B)
    // ---------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [ADDR_WIDTH-1:0]       s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [USER_WIDTH-1:0]       s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    input  logic [DATA_WIDTH-1:0]       s_axi_wdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [USER_WIDTH-1:0]       s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [USER_WIDTH-1:0]       s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // ---------------------------------------------------------------
    // AXI4 slave read channels (AR + R)
    // ---------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [ADDR_WIDTH-1:0]       s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [USER_WIDTH-1:0]       s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [DATA_WIDTH-1:0]       s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [USER_WIDTH-1:0]       s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    // Bulk-clear control + debug outputs (pass-through from sdpram_slave)
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,
    output logic [9:0]                  o_dbg_vr,
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd,
    output logic                        o_dbg_busy_wr,
    output logic                        o_dbg_busy_rd
);

    sdpram_slave #(
        .WR_PROTOCOL   ("AXI4"),
        .RD_PROTOCOL   ("AXI4"),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .USER_WIDTH    (USER_WIDTH),
        .MEM_DEPTH     (MEM_DEPTH),
        .SKID_DEPTH_AW (SKID_DEPTH_AW),
        .SKID_DEPTH_W  (SKID_DEPTH_W),
        .SKID_DEPTH_B  (SKID_DEPTH_B),
        .SKID_DEPTH_AR (SKID_DEPTH_AR),
        .SKID_DEPTH_R  (SKID_DEPTH_R)
    ) u_core (
        .aclk             (aclk),
        .aresetn          (aresetn),

        .s_axi_awid       (s_axi_awid),
        .s_axi_awaddr     (s_axi_awaddr),
        .s_axi_awlen      (s_axi_awlen),
        .s_axi_awsize     (s_axi_awsize),
        .s_axi_awburst    (s_axi_awburst),
        .s_axi_awlock     (s_axi_awlock),
        .s_axi_awcache    (s_axi_awcache),
        .s_axi_awprot     (s_axi_awprot),
        .s_axi_awqos      (s_axi_awqos),
        .s_axi_awregion   (s_axi_awregion),
        .s_axi_awuser     (s_axi_awuser),
        .s_axi_awvalid    (s_axi_awvalid),
        .s_axi_awready    (s_axi_awready),

        .s_axi_wdata      (s_axi_wdata),
        .s_axi_wstrb      (s_axi_wstrb),
        .s_axi_wlast      (s_axi_wlast),
        .s_axi_wuser      (s_axi_wuser),
        .s_axi_wvalid     (s_axi_wvalid),
        .s_axi_wready     (s_axi_wready),

        .s_axi_bid        (s_axi_bid),
        .s_axi_bresp      (s_axi_bresp),
        .s_axi_buser      (s_axi_buser),
        .s_axi_bvalid     (s_axi_bvalid),
        .s_axi_bready     (s_axi_bready),

        .s_axi_arid       (s_axi_arid),
        .s_axi_araddr     (s_axi_araddr),
        .s_axi_arlen      (s_axi_arlen),
        .s_axi_arsize     (s_axi_arsize),
        .s_axi_arburst    (s_axi_arburst),
        .s_axi_arlock     (s_axi_arlock),
        .s_axi_arcache    (s_axi_arcache),
        .s_axi_arprot     (s_axi_arprot),
        .s_axi_arqos      (s_axi_arqos),
        .s_axi_arregion   (s_axi_arregion),
        .s_axi_aruser     (s_axi_aruser),
        .s_axi_arvalid    (s_axi_arvalid),
        .s_axi_arready    (s_axi_arready),

        .s_axi_rid        (s_axi_rid),
        .s_axi_rdata      (s_axi_rdata),
        .s_axi_rresp      (s_axi_rresp),
        .s_axi_rlast      (s_axi_rlast),
        .s_axi_ruser      (s_axi_ruser),
        .s_axi_rvalid     (s_axi_rvalid),
        .s_axi_rready     (s_axi_rready),

        .i_cfg_start_clear (i_cfg_start_clear),
        .o_cfg_done_clear  (o_cfg_done_clear),
        .o_dbg_vr          (o_dbg_vr),
        .o_dbg_fub_vr      (o_dbg_fub_vr),
        .o_dbg_bram_wr     (o_dbg_bram_wr),
        .o_dbg_bram_rd     (o_dbg_bram_rd),
        .o_dbg_busy_wr     (o_dbg_busy_wr),
        .o_dbg_busy_rd     (o_dbg_busy_rd)
    );

endmodule : sdpram_slave_axi4_axi4
