// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_wr_cg
// Purpose: axil5_master_wr with clock gating
//
// Clock-gated wrapper around axil5_master_wr. ONE amba_clock_gate_ctrl gates the whole
// inner module; there are no per-domain gates. Functionally equivalent to the
// base module, minus the un-exported `busy` -- the wrapper consumes it as a
// wake term instead of forwarding it.
//
// Every READY this wrapper drives outward is forced low while cg_gating is
// high, so nothing is accepted into a stopped clock.
//
// One deliberate difference from the AXI4-Lite wrappers, which disagree with
// each other on this point: for a reverse channel the wake term includes BOTH
// the incoming valid and the valid this wrapper is presenting outward.
// axil4_slave_rd_cg does that and axil4_master_rd_cg does not. Extra wake
// terms can only make gating less aggressive, never incorrect, and this way a
// response beat still being offered cannot have the clock stopped underneath
// it -- so the safer of the two shapes is used uniformly.
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-01

`timescale 1ns / 1ps

module axil5_master_wr_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // AXI5-Lite ID and optional signal widths
    // AWID/BID and ARID/RID width (IHI 0022L Table A5.2: 0..32).
    // This is a Manager-side interface, where Table B2.2 makes the ID
    // optional (code YS): 0 means no ID -- the m_axil_ ID outputs are
    // driven 0 (the "tied LOW" of A5.1.1) and the ID inputs are ignored.
    parameter int ID_WIDTH           = 4,
    parameter int USER_WIDTH         = 4,

    // AXI5-Lite optional signal groups
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW    = 2,
    parameter int SKID_DEPTH_W     = 4,
    parameter int SKID_DEPTH_B     = 2,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int SW       = DW / 8,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // AW channel
    input  logic [IW-1:0]           fub_awid,
    input  logic [AW-1:0]           fub_awaddr,
    input  logic [2:0]              fub_awprot,
    input  logic [UW-1:0]           fub_awuser,
    input  logic                    fub_awtrace,
    input  logic                    fub_awvalid,
    output logic                    fub_awready,
    output logic [IW-1:0]           m_axil_awid,
    output logic [AW-1:0]           m_axil_awaddr,
    output logic [2:0]              m_axil_awprot,
    output logic [UW-1:0]           m_axil_awuser,
    output logic                    m_axil_awtrace,
    output logic                    m_axil_awvalid,
    input  logic                    m_axil_awready,

    // W channel
    input  logic [DW-1:0]           fub_wdata,
    input  logic [SW-1:0]           fub_wstrb,
    input  logic [UW-1:0]           fub_wuser,
    input  logic [PW-1:0]           fub_wpoison,
    input  logic                    fub_wvalid,
    output logic                    fub_wready,
    output logic [DW-1:0]           m_axil_wdata,
    output logic [SW-1:0]           m_axil_wstrb,
    output logic [UW-1:0]           m_axil_wuser,
    output logic [PW-1:0]           m_axil_wpoison,
    output logic                    m_axil_wvalid,
    input  logic                    m_axil_wready,

    // B channel
    input  logic [IW-1:0]           m_axil_bid,
    input  logic [1:0]              m_axil_bresp,
    input  logic [UW-1:0]           m_axil_buser,
    input  logic                    m_axil_btrace,
    input  logic                    m_axil_bvalid,
    output logic                    m_axil_bready,
    output logic [IW-1:0]           fub_bid,
    output logic [1:0]              fub_bresp,
    output logic [UW-1:0]           fub_buser,
    output logic                    fub_btrace,
    output logic                    fub_bvalid,
    input  logic                    fub_bready,

    // Clock gating status
    output logic                       cg_gating,         // Active gating indicator
    output logic                       cg_idle            // All buffers empty indicator
);

    // ---------------------------------------------------------------------
    // Elaboration-time parameter guard (the one sanctioned in-RTL check; see
    // vault/handbook/design/no-assertions-in-rtl.md). Checks nothing at run
    // time.
    //   AXIL_DATA_WIDTH: AXI5-Lite takes any AXI DATA_WIDTH -- 8, 16, 32, 64,
    //     128, 256, 512 or 1024 (IHI 0022L Table A3.19; Table B2.4 adds no
    //     AXI5-Lite constraint, unlike AXI4-Lite's 32/64 of IHI 0022H B1.1.2).
    //   ID_WIDTH: 0..32 (Table A5.2). Manager-side: 0 = no ID is legal (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_master_wr_cg: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 0 || ID_WIDTH > 32)
            $fatal(1, "axil5_master_wr_cg: ID_WIDTH=%0d out of range 0..32 (IHI 0022L Table A5.2)",
                   ID_WIDTH);
    end
`endif

    logic gated_aclk;
    logic user_valid;
    logic axi_valid;
    logic int_busy;
    logic int_awready;
    logic int_wready;
    logic int_bready;

    // A peer's READY must never appear in the activity term: a consumer
    // that parks its response-ready high while idle is behaving correctly,
    // and folding that in pins this block permanently awake and defeats
    // gating entirely -- the wrapper's only feature, silently dead. The
    // _mon_cg siblings documented this rule and obeyed it; these did not.
    assign user_valid = fub_awvalid || fub_wvalid || int_busy;  // fub_bvalid is in axi_valid
    assign axi_valid  = m_axil_awvalid || m_axil_wvalid || m_axil_bvalid || fub_bvalid;

    // Nothing is accepted into a stopped clock
    assign fub_awready = cg_gating ? 1'b0 : int_awready;
    assign fub_wready = cg_gating ? 1'b0 : int_wready;
    assign m_axil_bready = cg_gating ? 1'b0 : int_bready;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    axil5_master_wr #(
        .AXIL_ADDR_WIDTH    (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH    (AXIL_DATA_WIDTH),
        .ID_WIDTH           (ID_WIDTH),
        .USER_WIDTH         (USER_WIDTH),
        .ENABLE_USER        (ENABLE_USER),
        .ENABLE_TRACE       (ENABLE_TRACE),
        .ENABLE_POISON      (ENABLE_POISON),
        .SKID_DEPTH_AW      (SKID_DEPTH_AW),
        .SKID_DEPTH_W       (SKID_DEPTH_W),
        .SKID_DEPTH_B       (SKID_DEPTH_B)
    ) i_axil5_master_wr (
        .aclk                   (gated_aclk),      // gated
        .aresetn                (aresetn),

        .fub_awid               (fub_awid),
        .fub_awaddr             (fub_awaddr),
        .fub_awprot             (fub_awprot),
        .fub_awuser             (fub_awuser),
        .fub_awtrace            (fub_awtrace),
        .fub_awvalid            (fub_awvalid),
        .fub_awready            (int_awready),      // gated on the way out
        .m_axil_awid            (m_axil_awid),
        .m_axil_awaddr          (m_axil_awaddr),
        .m_axil_awprot          (m_axil_awprot),
        .m_axil_awuser          (m_axil_awuser),
        .m_axil_awtrace         (m_axil_awtrace),
        .m_axil_awvalid         (m_axil_awvalid),
        .m_axil_awready         (m_axil_awready),

        .fub_wdata              (fub_wdata),
        .fub_wstrb              (fub_wstrb),
        .fub_wuser              (fub_wuser),
        .fub_wpoison            (fub_wpoison),
        .fub_wvalid             (fub_wvalid),
        .fub_wready             (int_wready),      // gated on the way out
        .m_axil_wdata           (m_axil_wdata),
        .m_axil_wstrb           (m_axil_wstrb),
        .m_axil_wuser           (m_axil_wuser),
        .m_axil_wpoison         (m_axil_wpoison),
        .m_axil_wvalid          (m_axil_wvalid),
        .m_axil_wready          (m_axil_wready),

        .m_axil_bid             (m_axil_bid),
        .m_axil_bresp           (m_axil_bresp),
        .m_axil_buser           (m_axil_buser),
        .m_axil_btrace          (m_axil_btrace),
        .m_axil_bvalid          (m_axil_bvalid),
        .m_axil_bready          (int_bready),      // gated on the way out
        .fub_bid                (fub_bid),
        .fub_bresp              (fub_bresp),
        .fub_buser              (fub_buser),
        .fub_btrace             (fub_btrace),
        .fub_bvalid             (fub_bvalid),
        .fub_bready             (fub_bready),
        .busy                   (int_busy)
    );

endmodule : axil5_master_wr_cg
