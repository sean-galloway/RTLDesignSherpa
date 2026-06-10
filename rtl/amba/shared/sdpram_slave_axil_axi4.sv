// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave_axil_axi4
// Purpose: AXIL-write + AXI4-read protocol wrapper for sdpram_core.
//          Write side instantiates axil4_slave_wr (single-beat);
//          read side instantiates axi4_slave_rd (full AXI4 with id /
//          len / size / burst). The wrapper bridges the AXIL write
//          FUB into sdpram_core's AXI-shaped FUB with single-beat
//          defaults (awlen=0, awsize=$clog2(STRB_W), awburst=INCR,
//          awid=0).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module sdpram_slave_axil_axi4 #(
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

    localparam int STRB_W             = DATA_WIDTH / 8;
    localparam int FUB_AWSIZE_DEFAULT = $clog2(STRB_W);

    // ---------------------------------------------------------------
    // FUB nets -- AXIL on write side, AXI4 on read side
    // ---------------------------------------------------------------
    logic [ADDR_WIDTH-1:0]     fub_axil_awaddr;
    /* verilator lint_off UNUSED */
    logic [2:0]                fub_axil_awprot;
    logic                      fub_arlock_unused;
    logic [3:0]                fub_arcache_unused;
    logic [2:0]                fub_arprot_unused;
    logic [3:0]                fub_arqos_unused;
    logic [3:0]                fub_arregion_unused;
    logic [USER_WIDTH-1:0]     fub_aruser_unused;
    /* verilator lint_on UNUSED */
    logic                      fub_axil_awvalid, fub_axil_awready;
    logic [DATA_WIDTH-1:0]     fub_axil_wdata;
    logic [STRB_W-1:0]         fub_axil_wstrb;
    logic                      fub_axil_wvalid,  fub_axil_wready;
    logic [1:0]                fub_axil_bresp;
    logic                      fub_axil_bvalid,  fub_axil_bready;

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

    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH-1:0]   core_bid_unused;
    /* verilator lint_on UNUSED */

    assign s_axi_ruser = '0;

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

        .fub_awid     ('0),
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
        s_axi_rready,   s_axi_rvalid,
        s_axi_arready,  s_axi_arvalid,
        s_axil_bready,  s_axil_bvalid,
        s_axil_wready,  s_axil_wvalid,
        s_axil_awready, s_axil_awvalid
    };

    // WRAP-burst sim assertion on the AXI4 read side
    // synopsys translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && s_axi_arvalid && s_axi_arready) begin
            assert (s_axi_arburst != 2'b10)
                else $warning("%m: AR WRAP burst (arburst=%b) supported by axi_gen_addr but not yet validated", s_axi_arburst);
        end
    end
    // synopsys translate_on

endmodule : sdpram_slave_axil_axi4
