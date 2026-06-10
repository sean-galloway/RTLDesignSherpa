// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axil_axil
// Purpose: AXIL-write + AXIL-read protocol wrapper for sdpram_core.
//          Directly instantiates axil4_slave_wr + axil4_slave_rd (the
//          native AXIL skid leaf modules) and bridges their AXIL FUB
//          outputs into sdpram_core's AXI-shaped FUB by supplying
//          single-beat defaults (awlen=0, awsize=$clog2(STRB_W),
//          awburst=INCR, awid=0). No fake AXI4 fields are exposed at
//          the wrapper's external boundary -- the smell from the
//          legacy generate-if base is gone.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module sdpram_slave_axil_axil #(
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

    // Bulk-clear control + debug
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,
    output logic [9:0]                  o_dbg_vr,
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd,
    output logic                        o_dbg_busy_wr,
    output logic                        o_dbg_busy_rd
);

    // ---------------------------------------------------------------
    // Derived
    // ---------------------------------------------------------------
    localparam int STRB_W  = DATA_WIDTH / 8;
    localparam int FUB_AWSIZE_DEFAULT = $clog2(STRB_W);
    // AXIL has no transaction ID; carry a 1-bit zero through sdpram_core
    // for typing only.
    localparam int CORE_ID_WIDTH = 1;

    // ---------------------------------------------------------------
    // AXIL FUB nets between skid leaf modules and the wrapper
    // ---------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]     fub_axil_awaddr;
    /* verilator lint_off UNUSED */
    logic [2:0]                fub_axil_awprot;
    logic [2:0]                fub_axil_arprot;
    /* verilator lint_on UNUSED */
    logic                      fub_axil_awvalid, fub_axil_awready;
    logic [DATA_WIDTH-1:0]     fub_axil_wdata;
    logic [STRB_W-1:0]         fub_axil_wstrb;
    logic                      fub_axil_wvalid,  fub_axil_wready;
    logic [1:0]                fub_axil_bresp;
    logic                      fub_axil_bvalid,  fub_axil_bready;

    logic [ADDR_WIDTH-1:0]     fub_axil_araddr;
    logic                      fub_axil_arvalid, fub_axil_arready;
    logic [DATA_WIDTH-1:0]     fub_axil_rdata;
    logic [1:0]                fub_axil_rresp;
    logic                      fub_axil_rvalid,  fub_axil_rready;

    // sdpram_core FUB outputs we ignore on the AXIL side
    /* verilator lint_off UNUSED */
    logic [CORE_ID_WIDTH-1:0]  core_bid_unused;
    logic [CORE_ID_WIDTH-1:0]  core_rid_unused;
    logic                      core_rlast_unused;
    /* verilator lint_on UNUSED */

    // ---------------------------------------------------------------
    // Write-side AXIL skid
    // ---------------------------------------------------------------
    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (DATA_WIDTH),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),

        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),

        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),

        .fub_awaddr     (fub_axil_awaddr),
        .fub_awprot     (fub_axil_awprot),
        .fub_awvalid    (fub_axil_awvalid),
        .fub_awready    (fub_axil_awready),

        .fub_wdata      (fub_axil_wdata),
        .fub_wstrb      (fub_axil_wstrb),
        .fub_wvalid     (fub_axil_wvalid),
        .fub_wready     (fub_axil_wready),

        .fub_bresp      (fub_axil_bresp),
        .fub_bvalid     (fub_axil_bvalid),
        .fub_bready     (fub_axil_bready),

        .busy           (o_dbg_busy_wr)
    );

    // ---------------------------------------------------------------
    // Read-side AXIL skid
    // ---------------------------------------------------------------
    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (DATA_WIDTH),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),

        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),

        .fub_araddr     (fub_axil_araddr),
        .fub_arprot     (fub_axil_arprot),
        .fub_arvalid    (fub_axil_arvalid),
        .fub_arready    (fub_axil_arready),

        .fub_rdata      (fub_axil_rdata),
        .fub_rresp      (fub_axil_rresp),
        .fub_rvalid     (fub_axil_rvalid),
        .fub_rready     (fub_axil_rready),

        .busy           (o_dbg_busy_rd)
    );

    // ---------------------------------------------------------------
    // Shared backend (AXI-shaped FUB).  AXIL has no id/len/burst so
    // we feed sdpram_core single-beat INCR defaults.  These are the
    // only "fake" fields anywhere in the new design and they live in
    // exactly one place per wrapper.
    // ---------------------------------------------------------------
    sdpram_core #(
        .AXI_ID_WIDTH (CORE_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DATA_WIDTH),
        .MEM_DEPTH    (MEM_DEPTH)
    ) u_core (
        .aclk    (aclk),
        .aresetn (aresetn),

        .fub_awid     (1'b0),
        .fub_awaddr   (fub_axil_awaddr),
        .fub_awlen    (8'h00),
        .fub_awsize   (3'(FUB_AWSIZE_DEFAULT)),
        .fub_awburst  (2'b01),
        .fub_awvalid  (fub_axil_awvalid),
        .fub_awready  (fub_axil_awready),

        .fub_wdata    (fub_axil_wdata),
        .fub_wstrb    (fub_axil_wstrb),
        .fub_wvalid   (fub_axil_wvalid),
        .fub_wready   (fub_axil_wready),

        .fub_bid      (core_bid_unused),
        .fub_bresp    (fub_axil_bresp),
        .fub_bvalid   (fub_axil_bvalid),
        .fub_bready   (fub_axil_bready),

        .fub_arid     (1'b0),
        .fub_araddr   (fub_axil_araddr),
        .fub_arlen    (8'h00),
        .fub_arsize   (3'(FUB_AWSIZE_DEFAULT)),
        .fub_arburst  (2'b01),
        .fub_arvalid  (fub_axil_arvalid),
        .fub_arready  (fub_axil_arready),

        .fub_rid      (core_rid_unused),
        .fub_rdata    (fub_axil_rdata),
        .fub_rresp    (fub_axil_rresp),
        .fub_rlast    (core_rlast_unused),
        .fub_rvalid   (fub_axil_rvalid),
        .fub_rready   (fub_axil_rready),

        .i_cfg_start_clear (i_cfg_start_clear),
        .o_cfg_done_clear  (o_cfg_done_clear),

        .o_dbg_fub_vr  (o_dbg_fub_vr),
        .o_dbg_bram_wr (o_dbg_bram_wr),
        .o_dbg_bram_rd (o_dbg_bram_rd)
    );

    // External valid/ready taps (AW,W,B,AR,R)
    assign o_dbg_vr = {
        s_axil_rready,  s_axil_rvalid,
        s_axil_arready, s_axil_arvalid,
        s_axil_bready,  s_axil_bvalid,
        s_axil_wready,  s_axil_wvalid,
        s_axil_awready, s_axil_awvalid
    };

endmodule : sdpram_slave_axil_axil
