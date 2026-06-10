// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axi4_axil
// Purpose: AXI4-write + AXIL-read protocol wrapper for sdpram_core.
//          Write side instantiates axi4_slave_wr (full AXI4 with id /
//          len / size / burst); read side instantiates axil4_slave_rd
//          (single-beat). The wrapper bridges the AXIL read FUB into
//          sdpram_core's AXI-shaped FUB with single-beat defaults
//          (arlen=0, arsize=$clog2(STRB_W), arburst=INCR, arid=0).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module sdpram_slave_axi4_axil #(
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

    localparam int STRB_W            = DATA_WIDTH / 8;
    localparam int FUB_ARSIZE_DEFAULT = $clog2(STRB_W);

    // ---------------------------------------------------------------
    // FUB nets -- AXI4 on write side, AXIL on read side
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]   fub_awid;
    logic [ADDR_WIDTH-1:0]     fub_awaddr;
    logic [7:0]                fub_awlen;
    logic [2:0]                fub_awsize;
    logic [1:0]                fub_awburst;
    logic                      fub_awvalid, fub_awready;
    logic [DATA_WIDTH-1:0]     fub_wdata;
    logic [STRB_W-1:0]         fub_wstrb;
    logic                      fub_wvalid,  fub_wready;
    logic [AXI_ID_WIDTH-1:0]   fub_bid;
    logic [1:0]                fub_bresp;
    logic                      fub_bvalid,  fub_bready;

    logic [ADDR_WIDTH-1:0]     fub_axil_araddr;
    /* verilator lint_off UNUSED */
    logic [2:0]                fub_axil_arprot;
    // AXI4 fields not consumed by sdpram_core
    logic                      fub_awlock_unused;
    logic [3:0]                fub_awcache_unused;
    logic [2:0]                fub_awprot_unused;
    logic [3:0]                fub_awqos_unused;
    logic [3:0]                fub_awregion_unused;
    logic [USER_WIDTH-1:0]     fub_awuser_unused;
    logic                      fub_wlast_unused;
    logic [USER_WIDTH-1:0]     fub_wuser_unused;
    /* verilator lint_on UNUSED */
    logic                      fub_axil_arvalid, fub_axil_arready;
    logic [DATA_WIDTH-1:0]     fub_axil_rdata;
    logic [1:0]                fub_axil_rresp;
    logic                      fub_axil_rvalid,  fub_axil_rready;

    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH-1:0]   core_rid_unused;
    logic                      core_rlast_unused;
    /* verilator lint_on UNUSED */

    assign s_axi_buser = '0;

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

        .fub_arid     ('0),
        .fub_araddr   (fub_axil_araddr),
        .fub_arlen    (8'h00),
        .fub_arsize   (3'(FUB_ARSIZE_DEFAULT)),
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
        s_axi_bready,   s_axi_bvalid,
        s_axi_wready,   s_axi_wvalid,
        s_axi_awready,  s_axi_awvalid
    };

    // WRAP-burst sim assertion on the AXI4 write side
    // synopsys translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && s_axi_awvalid && s_axi_awready) begin
            assert (s_axi_awburst != 2'b10)
                else $warning("%m: AW WRAP burst (awburst=%b) supported by axi_gen_addr but not yet validated", s_axi_awburst);
        end
    end
    // synopsys translate_on

endmodule : sdpram_slave_axi4_axil
