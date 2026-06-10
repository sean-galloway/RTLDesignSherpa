// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axi4_axi4
// Purpose: AXI4-write + AXI4-read protocol wrapper for sdpram_core.
//          Directly instantiates axi4_slave_wr + axi4_slave_rd (the
//          native AXI4 skid leaf modules) and pipes their FUB-side
//          outputs into the shared sdpram_core backend. No string-
//          switch generate plumbing; no fake AXI4 fields. One of the
//          four protocol permutations:
//
//            sdpram_slave_axi4_axi4    -- AXI4 wr,  AXI4 rd   <-- this file
//            sdpram_slave_axi4_axil    -- AXI4 wr,  AXIL rd
//            sdpram_slave_axil_axi4    -- AXIL wr,  AXI4 rd
//            sdpram_slave_axil_axil    -- AXIL wr,  AXIL rd
//
// Subsystem: amba
// Author: sean galloway

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
    // FUB-side nets between the AXI4 skid leaf modules and sdpram_core
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]   fub_awid;
    logic [ADDR_WIDTH-1:0]     fub_awaddr;
    logic [7:0]                fub_awlen;
    logic [2:0]                fub_awsize;
    logic [1:0]                fub_awburst;
    logic                      fub_awvalid, fub_awready;
    logic [DATA_WIDTH-1:0]     fub_wdata;
    logic [DATA_WIDTH/8-1:0]   fub_wstrb;
    logic                      fub_wvalid,  fub_wready;
    logic [AXI_ID_WIDTH-1:0]   fub_bid;
    logic [1:0]                fub_bresp;
    logic                      fub_bvalid,  fub_bready;

    logic [AXI_ID_WIDTH-1:0]   fub_arid;
    logic [ADDR_WIDTH-1:0]     fub_araddr;
    logic [7:0]                fub_arlen;
    logic [2:0]                fub_arsize;
    logic [1:0]                fub_arburst;
    logic                      fub_arvalid, fub_arready;
    logic [AXI_ID_WIDTH-1:0]   fub_rid;
    logic [DATA_WIDTH-1:0]     fub_rdata;
    logic [1:0]                fub_rresp;
    logic                      fub_rlast;
    logic                      fub_rvalid,  fub_rready;

    // AXI4-only FUB nets that the skid leaf modules carry through but
    // sdpram_core ignores (lock / cache / qos / region / user / wlast).
    /* verilator lint_off UNUSED */
    logic                      fub_awlock_unused;
    logic [3:0]                fub_awcache_unused;
    logic [2:0]                fub_awprot_unused;
    logic [3:0]                fub_awqos_unused;
    logic [3:0]                fub_awregion_unused;
    logic [USER_WIDTH-1:0]     fub_awuser_unused;
    logic                      fub_wlast_unused;
    logic [USER_WIDTH-1:0]     fub_wuser_unused;
    logic                      fub_arlock_unused;
    logic [3:0]                fub_arcache_unused;
    logic [2:0]                fub_arprot_unused;
    logic [3:0]                fub_arqos_unused;
    logic [3:0]                fub_arregion_unused;
    logic [USER_WIDTH-1:0]     fub_aruser_unused;
    /* verilator lint_on UNUSED */

    // sdpram_core does not preserve user across the BRAM, so the AXI4
    // wrappers hardcode buser / ruser to zero (matches legacy behaviour).
    assign s_axi_buser = '0;
    assign s_axi_ruser = '0;

    // ---------------------------------------------------------------
    // Write-side AXI4 skid
    // ---------------------------------------------------------------
    axi4_slave_wr #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH),
        .AXI_USER_WIDTH (USER_WIDTH),
        .SKID_DEPTH_AW  (SKID_DEPTH_AW),
        .SKID_DEPTH_W   (SKID_DEPTH_W),
        .SKID_DEPTH_B   (SKID_DEPTH_B)
    ) u_axi4_wr (
        .aclk            (aclk),
        .aresetn         (aresetn),

        .s_axi_awid      (s_axi_awid),
        .s_axi_awaddr    (s_axi_awaddr),
        .s_axi_awlen     (s_axi_awlen),
        .s_axi_awsize    (s_axi_awsize),
        .s_axi_awburst   (s_axi_awburst),
        .s_axi_awlock    (s_axi_awlock),
        .s_axi_awcache   (s_axi_awcache),
        .s_axi_awprot    (s_axi_awprot),
        .s_axi_awqos     (s_axi_awqos),
        .s_axi_awregion  (s_axi_awregion),
        .s_axi_awuser    (s_axi_awuser),
        .s_axi_awvalid   (s_axi_awvalid),
        .s_axi_awready   (s_axi_awready),

        .s_axi_wdata     (s_axi_wdata),
        .s_axi_wstrb     (s_axi_wstrb),
        .s_axi_wlast     (s_axi_wlast),
        .s_axi_wuser     (s_axi_wuser),
        .s_axi_wvalid    (s_axi_wvalid),
        .s_axi_wready    (s_axi_wready),

        .s_axi_bid       (s_axi_bid),
        .s_axi_bresp     (s_axi_bresp),
        .s_axi_buser     (/* unused */),
        .s_axi_bvalid    (s_axi_bvalid),
        .s_axi_bready    (s_axi_bready),

        .fub_axi_awid     (fub_awid),
        .fub_axi_awaddr   (fub_awaddr),
        .fub_axi_awlen    (fub_awlen),
        .fub_axi_awsize   (fub_awsize),
        .fub_axi_awburst  (fub_awburst),
        .fub_axi_awlock   (fub_awlock_unused),
        .fub_axi_awcache  (fub_awcache_unused),
        .fub_axi_awprot   (fub_awprot_unused),
        .fub_axi_awqos    (fub_awqos_unused),
        .fub_axi_awregion (fub_awregion_unused),
        .fub_axi_awuser   (fub_awuser_unused),
        .fub_axi_awvalid  (fub_awvalid),
        .fub_axi_awready  (fub_awready),

        .fub_axi_wdata    (fub_wdata),
        .fub_axi_wstrb    (fub_wstrb),
        .fub_axi_wlast    (fub_wlast_unused),
        .fub_axi_wuser    (fub_wuser_unused),
        .fub_axi_wvalid   (fub_wvalid),
        .fub_axi_wready   (fub_wready),

        .fub_axi_bid      (fub_bid),
        .fub_axi_bresp    (fub_bresp),
        .fub_axi_buser    ('0),
        .fub_axi_bvalid   (fub_bvalid),
        .fub_axi_bready   (fub_bready),

        .busy             (o_dbg_busy_wr)
    );

    // ---------------------------------------------------------------
    // Read-side AXI4 skid
    // ---------------------------------------------------------------
    axi4_slave_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH),
        .AXI_USER_WIDTH (USER_WIDTH),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_R   (SKID_DEPTH_R)
    ) u_axi4_rd (
        .aclk            (aclk),
        .aresetn         (aresetn),

        .s_axi_arid      (s_axi_arid),
        .s_axi_araddr    (s_axi_araddr),
        .s_axi_arlen     (s_axi_arlen),
        .s_axi_arsize    (s_axi_arsize),
        .s_axi_arburst   (s_axi_arburst),
        .s_axi_arlock    (s_axi_arlock),
        .s_axi_arcache   (s_axi_arcache),
        .s_axi_arprot    (s_axi_arprot),
        .s_axi_arqos     (s_axi_arqos),
        .s_axi_arregion  (s_axi_arregion),
        .s_axi_aruser    (s_axi_aruser),
        .s_axi_arvalid   (s_axi_arvalid),
        .s_axi_arready   (s_axi_arready),

        .s_axi_rid       (s_axi_rid),
        .s_axi_rdata     (s_axi_rdata),
        .s_axi_rresp     (s_axi_rresp),
        .s_axi_rlast     (s_axi_rlast),
        .s_axi_ruser     (/* unused */),
        .s_axi_rvalid    (s_axi_rvalid),
        .s_axi_rready    (s_axi_rready),

        .fub_axi_arid     (fub_arid),
        .fub_axi_araddr   (fub_araddr),
        .fub_axi_arlen    (fub_arlen),
        .fub_axi_arsize   (fub_arsize),
        .fub_axi_arburst  (fub_arburst),
        .fub_axi_arlock   (fub_arlock_unused),
        .fub_axi_arcache  (fub_arcache_unused),
        .fub_axi_arprot   (fub_arprot_unused),
        .fub_axi_arqos    (fub_arqos_unused),
        .fub_axi_arregion (fub_arregion_unused),
        .fub_axi_aruser   (fub_aruser_unused),
        .fub_axi_arvalid  (fub_arvalid),
        .fub_axi_arready  (fub_arready),

        .fub_axi_rid      (fub_rid),
        .fub_axi_rdata    (fub_rdata),
        .fub_axi_rresp    (fub_rresp),
        .fub_axi_rlast    (fub_rlast),
        .fub_axi_ruser    ('0),
        .fub_axi_rvalid   (fub_rvalid),
        .fub_axi_rready   (fub_rready),

        .busy             (o_dbg_busy_rd)
    );

    // ---------------------------------------------------------------
    // Shared backend
    // ---------------------------------------------------------------
    sdpram_core #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DATA_WIDTH),
        .MEM_DEPTH    (MEM_DEPTH)
    ) u_core (
        .aclk    (aclk),
        .aresetn (aresetn),

        .fub_awid     (fub_awid),
        .fub_awaddr   (fub_awaddr),
        .fub_awlen    (fub_awlen),
        .fub_awsize   (fub_awsize),
        .fub_awburst  (fub_awburst),
        .fub_awvalid  (fub_awvalid),
        .fub_awready  (fub_awready),
        .fub_wdata    (fub_wdata),
        .fub_wstrb    (fub_wstrb),
        .fub_wvalid   (fub_wvalid),
        .fub_wready   (fub_wready),
        .fub_bid      (fub_bid),
        .fub_bresp    (fub_bresp),
        .fub_bvalid   (fub_bvalid),
        .fub_bready   (fub_bready),

        .fub_arid     (fub_arid),
        .fub_araddr   (fub_araddr),
        .fub_arlen    (fub_arlen),
        .fub_arsize   (fub_arsize),
        .fub_arburst  (fub_arburst),
        .fub_arvalid  (fub_arvalid),
        .fub_arready  (fub_arready),
        .fub_rid      (fub_rid),
        .fub_rdata    (fub_rdata),
        .fub_rresp    (fub_rresp),
        .fub_rlast    (fub_rlast),
        .fub_rvalid   (fub_rvalid),
        .fub_rready   (fub_rready),

        .i_cfg_start_clear (i_cfg_start_clear),
        .o_cfg_done_clear  (o_cfg_done_clear),

        .o_dbg_fub_vr  (o_dbg_fub_vr),
        .o_dbg_bram_wr (o_dbg_bram_wr),
        .o_dbg_bram_rd (o_dbg_bram_rd)
    );

    // External valid/ready taps (AW,W,B,AR,R)
    assign o_dbg_vr = {
        s_axi_rready,  s_axi_rvalid,
        s_axi_arready, s_axi_arvalid,
        s_axi_bready,  s_axi_bvalid,
        s_axi_wready,  s_axi_wvalid,
        s_axi_awready, s_axi_awvalid
    };

    // WRAP-burst sim assertions
    // synopsys translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && s_axi_awvalid && s_axi_awready) begin
            assert (s_axi_awburst != 2'b10)
                else $warning("%m: AW WRAP burst (awburst=%b) supported by axi_gen_addr but not yet validated", s_axi_awburst);
        end
        if (aresetn && s_axi_arvalid && s_axi_arready) begin
            assert (s_axi_arburst != 2'b10)
                else $warning("%m: AR WRAP burst (arburst=%b) supported by axi_gen_addr but not yet validated", s_axi_arburst);
        end
    end
    // synopsys translate_on

endmodule : sdpram_slave_axi4_axi4
