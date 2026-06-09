// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axil
// Purpose: Thin wrapper around sdpram_slave that fixes both sides to
//          AXIL and exposes ONLY AXIL-shaped ports. Use this when the
//          caller's fabric is pure AXIL -- the port list contains no
//          AXI4-only fields (no awid/awlen/awsize/awburst/awlock/
//          awcache/awqos/awregion/awuser/wlast/wuser/bid/buser nor the
//          AR/R equivalents), and the port names use the `s_axil_*`
//          prefix per AXIL convention.
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-06-09
//
// For pure AXI4 fabrics, see `sdpram_slave_axi4.sv`. For heterogeneous
// configurations (AXI4 write + AXIL read or vice versa), instantiate
// `sdpram_slave` directly with the desired WR_PROTOCOL / RD_PROTOCOL
// string parameters.

`timescale 1ns / 1ps

module sdpram_slave_axil #(
    parameter int    ADDR_WIDTH    = 32,
    parameter int    DATA_WIDTH    = 64,
    parameter int    MEM_DEPTH     = 1024,
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

    // The underlying sdpram_slave module has an AXI4-shaped port list.
    // In AXIL mode it ignores id/len/size/burst/lock/cache/qos/region/
    // user/last on inputs and drives those outputs to 0. We tie all
    // AXI4-only inputs to 0 here so the AXIL caller never has to.
    //
    // sdpram_slave's AXIL skids carry the channel via the s_axi_* port
    // names (awaddr/awprot/awvalid/awready/wdata/wstrb/wvalid/wready/
    // bresp/bvalid/bready and the AR/R equivalents); this wrapper just
    // renames them to s_axil_* on the outside.

    logic [1:0]               b_dummy_id;     // sdpram_slave drives 0
    logic                     b_dummy_user;   // sdpram_slave drives 0
    logic [1:0]               r_dummy_id;     // sdpram_slave drives 0
    logic                     r_dummy_user;   // sdpram_slave drives 0
    /* verilator lint_off UNUSED */
    logic                     r_dummy_rlast;  // always 1 in AXIL mode
    /* verilator lint_on UNUSED */

    sdpram_slave #(
        .WR_PROTOCOL   ("AXIL"),
        .RD_PROTOCOL   ("AXIL"),
        // ID/USER widths irrelevant in AXIL mode (skid ties to 0
        // internally) -- pass 2/1 just to give the AXI4-shaped port
        // a defined width.
        .AXI_ID_WIDTH  (2),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .USER_WIDTH    (1),
        .MEM_DEPTH     (MEM_DEPTH),
        .SKID_DEPTH_AW (SKID_DEPTH_AW),
        .SKID_DEPTH_W  (SKID_DEPTH_W),
        .SKID_DEPTH_B  (SKID_DEPTH_B),
        .SKID_DEPTH_AR (SKID_DEPTH_AR),
        .SKID_DEPTH_R  (SKID_DEPTH_R)
    ) u_core (
        .aclk             (aclk),
        .aresetn          (aresetn),

        // Write channels: drive AXIL on the s_axi_* ports (sdpram_slave's
        // AXIL skid picks these up), tie off AXI4-only inputs.
        .s_axi_awid       (2'b00),
        .s_axi_awaddr     (s_axil_awaddr),
        .s_axi_awlen      (8'h00),
        .s_axi_awsize     (3'h0),
        .s_axi_awburst    (2'b00),
        .s_axi_awlock     (1'b0),
        .s_axi_awcache    (4'h0),
        .s_axi_awprot     (s_axil_awprot),
        .s_axi_awqos      (4'h0),
        .s_axi_awregion   (4'h0),
        .s_axi_awuser     (1'b0),
        .s_axi_awvalid    (s_axil_awvalid),
        .s_axi_awready    (s_axil_awready),

        .s_axi_wdata      (s_axil_wdata),
        .s_axi_wstrb      (s_axil_wstrb),
        .s_axi_wlast      (1'b1),
        .s_axi_wuser      (1'b0),
        .s_axi_wvalid     (s_axil_wvalid),
        .s_axi_wready     (s_axil_wready),

        .s_axi_bid        (b_dummy_id),
        .s_axi_bresp      (s_axil_bresp),
        .s_axi_buser      (b_dummy_user),
        .s_axi_bvalid     (s_axil_bvalid),
        .s_axi_bready     (s_axil_bready),

        // Read channels: same pattern, AXIL through s_axi_* port names.
        .s_axi_arid       (2'b00),
        .s_axi_araddr     (s_axil_araddr),
        .s_axi_arlen      (8'h00),
        .s_axi_arsize     (3'h0),
        .s_axi_arburst    (2'b00),
        .s_axi_arlock     (1'b0),
        .s_axi_arcache    (4'h0),
        .s_axi_arprot     (s_axil_arprot),
        .s_axi_arqos      (4'h0),
        .s_axi_arregion   (4'h0),
        .s_axi_aruser     (1'b0),
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

    // sdpram_slave guarantees these are zero in AXIL mode; consume them
    // here so verilator doesn't flag UNUSED.
    /* verilator lint_off UNUSED */
    wire _unused_axil = &{1'b0, b_dummy_id, b_dummy_user, r_dummy_id,
                          r_dummy_user, r_dummy_rlast};
    /* verilator lint_on UNUSED */

endmodule : sdpram_slave_axil
