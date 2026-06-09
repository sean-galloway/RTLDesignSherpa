// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axil_axi4
// Purpose: AXIL write + AXI4 read shape of sdpram_slave. Write side
//          exposes the AXIL port set (s_axil_aw*/w*/b*); read side
//          exposes the full AXI4 port set (s_axi_ar*/r*). One of the
//          four protocol permutations -- see header in
//          `sdpram_slave_axi4_axi4.sv`. All four share the same backend
//          (`sdpram_slave.sv`).
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-06-09

`timescale 1ns / 1ps

module sdpram_slave_axil_axi4 #(
    parameter int    AXI_ID_WIDTH = 8,           // read side only
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    USER_WIDTH   = 1,           // read side only
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
    // AXIL slave write channels (AW + W + B)
    // ---------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]       s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,

    input  logic [DATA_WIDTH-1:0]       s_axil_wdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,

    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,

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

    // Bulk-clear control + debug outputs
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,
    output logic [9:0]                  o_dbg_vr,
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd,
    output logic                        o_dbg_busy_wr,
    output logic                        o_dbg_busy_rd
);

    // Sink-side AXI4-only outputs the write AXIL skid would otherwise
    // drive on the backend's s_axi_* port. Backend ties them to 0.
    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH-1:0]            b_dummy_id;
    logic [USER_WIDTH-1:0]              b_dummy_user;
    /* verilator lint_on UNUSED */

    sdpram_slave #(
        .WR_PROTOCOL   ("AXIL"),
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

        // Write side: drive AXIL onto the backend's AXI4-shaped write port,
        // tie off the AXI4-only inputs. Backend's AXIL skid picks up
        // awaddr/awprot/awvalid/awready and wdata/wstrb/wvalid/wready.
        .s_axi_awid       ({AXI_ID_WIDTH{1'b0}}),
        .s_axi_awaddr     (s_axil_awaddr),
        .s_axi_awlen      (8'h00),
        .s_axi_awsize     (3'h0),
        .s_axi_awburst    (2'b00),
        .s_axi_awlock     (1'b0),
        .s_axi_awcache    (4'h0),
        .s_axi_awprot     (s_axil_awprot),
        .s_axi_awqos      (4'h0),
        .s_axi_awregion   (4'h0),
        .s_axi_awuser     ({USER_WIDTH{1'b0}}),
        .s_axi_awvalid    (s_axil_awvalid),
        .s_axi_awready    (s_axil_awready),

        .s_axi_wdata      (s_axil_wdata),
        .s_axi_wstrb      (s_axil_wstrb),
        .s_axi_wlast      (1'b1),
        .s_axi_wuser      ({USER_WIDTH{1'b0}}),
        .s_axi_wvalid     (s_axil_wvalid),
        .s_axi_wready     (s_axil_wready),

        .s_axi_bid        (b_dummy_id),
        .s_axi_bresp      (s_axil_bresp),
        .s_axi_buser      (b_dummy_user),
        .s_axi_bvalid     (s_axil_bvalid),
        .s_axi_bready     (s_axil_bready),

        // Read side: pass AXI4 ports straight through.
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

endmodule : sdpram_slave_axil_axi4
