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

    // AXI5-Lite optional signal widths
    parameter int USER_WIDTH         = 4,
    parameter int LOOP_WIDTH         = 3,
    parameter int MPAM_WIDTH         = 11,
    parameter int MECID_WIDTH        = 16,
    parameter int NSAID_WIDTH        = 4,

    // AXI5-Lite optional signal groups
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_LOOP        = 1,
    parameter bit ENABLE_MPAM        = 1,
    parameter bit ENABLE_MECID       = 1,
    parameter bit ENABLE_NSAID       = 1,
    parameter bit ENABLE_POISON      = 1,
    parameter bit ENABLE_LOCK        = 1,

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
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
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
    input  logic [AW-1:0]           fub_awaddr,
    input  logic [2:0]              fub_awprot,
    input  logic                    fub_awlock,
    input  logic [UW-1:0]           fub_awuser,
    input  logic                    fub_awtrace,
    input  logic [LW-1:0]           fub_awloop,
    input  logic [MW-1:0]           fub_awmpam,
    input  logic [EW-1:0]           fub_awmecid,
    input  logic [NW-1:0]           fub_awnsaid,
    input  logic                    fub_awvalid,
    output logic                    fub_awready,
    output logic [AW-1:0]           m_axil_awaddr,
    output logic [2:0]              m_axil_awprot,
    output logic                    m_axil_awlock,
    output logic [UW-1:0]           m_axil_awuser,
    output logic                    m_axil_awtrace,
    output logic [LW-1:0]           m_axil_awloop,
    output logic [MW-1:0]           m_axil_awmpam,
    output logic [EW-1:0]           m_axil_awmecid,
    output logic [NW-1:0]           m_axil_awnsaid,
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
    input  logic [1:0]              m_axil_bresp,
    input  logic [UW-1:0]           m_axil_buser,
    input  logic                    m_axil_btrace,
    input  logic [LW-1:0]           m_axil_bloop,
    input  logic                    m_axil_bvalid,
    output logic                    m_axil_bready,
    output logic [1:0]              fub_bresp,
    output logic [UW-1:0]           fub_buser,
    output logic                    fub_btrace,
    output logic [LW-1:0]           fub_bloop,
    output logic                    fub_bvalid,
    input  logic                    fub_bready,

    // Clock gating status
    output logic                       cg_gating,         // Active gating indicator
    output logic                       cg_idle            // All buffers empty indicator
);

    logic gated_aclk;
    logic user_valid;
    logic axi_valid;
    logic int_busy;
    logic int_awready;
    logic int_wready;
    logic int_bready;

    assign user_valid = fub_awvalid || fub_wvalid || fub_bready || int_busy;
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
        .USER_WIDTH         (USER_WIDTH),
        .LOOP_WIDTH         (LOOP_WIDTH),
        .MPAM_WIDTH         (MPAM_WIDTH),
        .MECID_WIDTH        (MECID_WIDTH),
        .NSAID_WIDTH        (NSAID_WIDTH),
        .ENABLE_USER        (ENABLE_USER),
        .ENABLE_TRACE       (ENABLE_TRACE),
        .ENABLE_LOOP        (ENABLE_LOOP),
        .ENABLE_MPAM        (ENABLE_MPAM),
        .ENABLE_MECID       (ENABLE_MECID),
        .ENABLE_NSAID       (ENABLE_NSAID),
        .ENABLE_POISON      (ENABLE_POISON),
        .ENABLE_LOCK        (ENABLE_LOCK),
        .SKID_DEPTH_AW      (SKID_DEPTH_AW),
        .SKID_DEPTH_W       (SKID_DEPTH_W),
        .SKID_DEPTH_B       (SKID_DEPTH_B)
    ) i_axil5_master_wr (
        .aclk                   (gated_aclk),      // gated
        .aresetn                (aresetn),

        .fub_awaddr             (fub_awaddr),
        .fub_awprot             (fub_awprot),
        .fub_awlock             (fub_awlock),
        .fub_awuser             (fub_awuser),
        .fub_awtrace            (fub_awtrace),
        .fub_awloop             (fub_awloop),
        .fub_awmpam             (fub_awmpam),
        .fub_awmecid            (fub_awmecid),
        .fub_awnsaid            (fub_awnsaid),
        .fub_awvalid            (fub_awvalid),
        .fub_awready            (int_awready),      // gated on the way out
        .m_axil_awaddr          (m_axil_awaddr),
        .m_axil_awprot          (m_axil_awprot),
        .m_axil_awlock          (m_axil_awlock),
        .m_axil_awuser          (m_axil_awuser),
        .m_axil_awtrace         (m_axil_awtrace),
        .m_axil_awloop          (m_axil_awloop),
        .m_axil_awmpam          (m_axil_awmpam),
        .m_axil_awmecid         (m_axil_awmecid),
        .m_axil_awnsaid         (m_axil_awnsaid),
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

        .m_axil_bresp           (m_axil_bresp),
        .m_axil_buser           (m_axil_buser),
        .m_axil_btrace          (m_axil_btrace),
        .m_axil_bloop           (m_axil_bloop),
        .m_axil_bvalid          (m_axil_bvalid),
        .m_axil_bready          (int_bready),      // gated on the way out
        .fub_bresp              (fub_bresp),
        .fub_buser              (fub_buser),
        .fub_btrace             (fub_btrace),
        .fub_bloop              (fub_bloop),
        .fub_bvalid             (fub_bvalid),
        .fub_bready             (fub_bready),
        .busy                   (int_busy)
    );

endmodule : axil5_master_wr_cg
