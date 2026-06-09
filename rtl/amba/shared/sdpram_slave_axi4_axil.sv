// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axi4_axil
// Purpose: AXI4 write + AXIL read shape of sdpram_slave. Write side
//          exposes the full AXI4 port set (s_axi_aw*/w*/b*); read side
//          exposes the AXIL port set (s_axil_ar*/r*). One of the four
//          protocol permutations -- see header in
//          `sdpram_slave_axi4_axi4.sv`. All four share the same backend
//          (`sdpram_slave.sv`).
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-06-09

`timescale 1ns / 1ps

module sdpram_slave_axi4_axil #(
    parameter int    AXI_ID_WIDTH = 8,           // write side only
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    USER_WIDTH   = 1,           // write side only
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
    // AXIL slave read channels (AR + R)
    // ---------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]       s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,

    output logic [DATA_WIDTH-1:0]       s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

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

    // Sink-side AXI4-only outputs the read AXIL skid would otherwise
    // drive on the backend's s_axi_* port. Backend ties them to 0.
    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH-1:0]            r_dummy_id;
    logic                               r_dummy_rlast;
    logic [USER_WIDTH-1:0]              r_dummy_user;
    /* verilator lint_on UNUSED */

    sdpram_slave #(
        .WR_PROTOCOL   ("AXI4"),
        .RD_PROTOCOL   ("AXIL"),
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

        // Write side: pass AXI4 ports straight through.
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

        // Read side: drive AXIL onto the backend's AXI4-shaped read port,
        // tie off the AXI4-only inputs. Backend's AXIL skid picks up
        // araddr/arprot/arvalid/arready and rdata/rresp/rvalid/rready.
        .s_axi_arid       ({AXI_ID_WIDTH{1'b0}}),
        .s_axi_araddr     (s_axil_araddr),
        .s_axi_arlen      (8'h00),
        .s_axi_arsize     (3'h0),
        .s_axi_arburst    (2'b00),
        .s_axi_arlock     (1'b0),
        .s_axi_arcache    (4'h0),
        .s_axi_arprot     (s_axil_arprot),
        .s_axi_arqos      (4'h0),
        .s_axi_arregion   (4'h0),
        .s_axi_aruser     ({USER_WIDTH{1'b0}}),
        .s_axi_arvalid    (s_axil_arvalid),
        .s_axi_arready    (s_axil_arready),

        .s_axi_rid        (r_dummy_id),
        .s_axi_rdata      (s_axil_rdata),
        .s_axi_rresp      (s_axil_rresp),
        .s_axi_rlast      (r_dummy_rlast),
        .s_axi_ruser      (r_dummy_user),
        .s_axi_rvalid     (s_axil_rvalid),
        .s_axi_rready     (s_axil_rready),

        .i_cfg_start_clear (i_cfg_start_clear),
        .o_cfg_done_clear  (o_cfg_done_clear),
        .o_dbg_vr          (o_dbg_vr),
        .o_dbg_fub_vr      (o_dbg_fub_vr),
        .o_dbg_bram_wr     (o_dbg_bram_wr),
        .o_dbg_bram_rd     (o_dbg_bram_rd),
        .o_dbg_busy_wr     (o_dbg_busy_wr),
        .o_dbg_busy_rd     (o_dbg_busy_rd)
    );

endmodule : sdpram_slave_axi4_axil
