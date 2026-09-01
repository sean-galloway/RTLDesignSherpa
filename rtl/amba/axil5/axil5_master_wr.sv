// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_wr
// Purpose: AXI5-Lite write master transport
//
// AXI5-Lite transport. Structurally this is axil4_master_wr with the AXI5-Lite optional
// signal groups added. Each group is gated by its own ENABLE_* parameter and
// contributes to the packed SKID payload only when enabled, so a build with
// every group disabled has the same payload width and the same behaviour as
// the AXI4-Lite module of the same name -- which is the property
// val/amba/test_axil5_master_rd.py relies on.
//
// It transports; it does not interpret. MPAM, MECID, NSAID, LOOP and TRACE
// are carried end to end unmodified. POISON is carried, never generated and
// never checked. LOCK is carried with no exclusive-access monitor behind it.
// Those behaviours belong to the endpoints on either side.
//
// A disabled group's output is driven to zero rather than left dangling, so
// an integrator who disables a group downstream of one that enables it sees a
// defined value instead of X.
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-01

`timescale 1ns / 1ps

module axil5_master_wr
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

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
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

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int SW       = DW / 8,
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int AWSize = AW + 3 +
                             (ENABLE_LOCK ? 1 : 0) +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_MPAM ? MW : 0) +
                             (ENABLE_MECID ? EW : 0) +
                             (ENABLE_NSAID ? NW : 0),

    parameter int WSize  = DW + SW +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_POISON ? PW : 0),

    parameter int BSize  = 2 +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AW channel: fub_ -> m_axil_
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

    // W channel: fub_ -> m_axil_
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

    // B channel: m_axil_ -> fub_
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

    // Status output for clock gating
    output logic                       busy
);

    // ---------------------------------------------------------------------
    // AW channel
    // ---------------------------------------------------------------------
    logic [AWSize-1:0] w_aw_wr_data, w_aw_rd_data;
    logic [3:0]        w_aw_count;

    always_comb begin
        automatic int idx = 0;
        w_aw_wr_data[idx +: AW] = fub_awaddr;
        idx += AW;
        w_aw_wr_data[idx +: 3] = fub_awprot;
        idx += 3;
        if (ENABLE_LOCK) begin
            w_aw_wr_data[idx +: 1] = fub_awlock;
            idx += 1;
        end
        if (ENABLE_USER) begin
            w_aw_wr_data[idx +: UW] = fub_awuser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_aw_wr_data[idx +: 1] = fub_awtrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_aw_wr_data[idx +: LW] = fub_awloop;
            idx += LW;
        end
        if (ENABLE_MPAM) begin
            w_aw_wr_data[idx +: MW] = fub_awmpam;
            idx += MW;
        end
        if (ENABLE_MECID) begin
            w_aw_wr_data[idx +: EW] = fub_awmecid;
            idx += EW;
        end
        if (ENABLE_NSAID) begin
            w_aw_wr_data[idx +: NW] = fub_awnsaid;
            idx += NW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) aw_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_awvalid),
        .wr_ready    (fub_awready),
        .wr_data     (w_aw_wr_data),
        .rd_valid    (m_axil_awvalid),
        .rd_ready    (m_axil_awready),
        .rd_count    (w_aw_count),
        .rd_data     (w_aw_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        m_axil_awaddr = w_aw_rd_data[idx +: AW];
        idx += AW;
        m_axil_awprot = w_aw_rd_data[idx +: 3];
        idx += 3;
        if (ENABLE_LOCK) begin
            m_axil_awlock = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axil_awlock = 1'b0;
        end
        if (ENABLE_USER) begin
            m_axil_awuser = w_aw_rd_data[idx +: UW];
            idx += UW;
        end else begin
            m_axil_awuser = '0;
        end
        if (ENABLE_TRACE) begin
            m_axil_awtrace = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axil_awtrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            m_axil_awloop = w_aw_rd_data[idx +: LW];
            idx += LW;
        end else begin
            m_axil_awloop = '0;
        end
        if (ENABLE_MPAM) begin
            m_axil_awmpam = w_aw_rd_data[idx +: MW];
            idx += MW;
        end else begin
            m_axil_awmpam = '0;
        end
        if (ENABLE_MECID) begin
            m_axil_awmecid = w_aw_rd_data[idx +: EW];
            idx += EW;
        end else begin
            m_axil_awmecid = '0;
        end
        if (ENABLE_NSAID) begin
            m_axil_awnsaid = w_aw_rd_data[idx +: NW];
            idx += NW;
        end else begin
            m_axil_awnsaid = '0;
        end
    end

    // ---------------------------------------------------------------------
    // W channel
    // ---------------------------------------------------------------------
    logic [WSize-1:0] w_w_wr_data, w_w_rd_data;
    logic [3:0]        w_w_count;

    always_comb begin
        automatic int idx = 0;
        w_w_wr_data[idx +: DW] = fub_wdata;
        idx += DW;
        w_w_wr_data[idx +: SW] = fub_wstrb;
        idx += SW;
        if (ENABLE_USER) begin
            w_w_wr_data[idx +: UW] = fub_wuser;
            idx += UW;
        end
        if (ENABLE_POISON) begin
            w_w_wr_data[idx +: PW] = fub_wpoison;
            idx += PW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) w_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_wvalid),
        .wr_ready    (fub_wready),
        .wr_data     (w_w_wr_data),
        .rd_valid    (m_axil_wvalid),
        .rd_ready    (m_axil_wready),
        .rd_count    (w_w_count),
        .rd_data     (w_w_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        m_axil_wdata = w_w_rd_data[idx +: DW];
        idx += DW;
        m_axil_wstrb = w_w_rd_data[idx +: SW];
        idx += SW;
        if (ENABLE_USER) begin
            m_axil_wuser = w_w_rd_data[idx +: UW];
            idx += UW;
        end else begin
            m_axil_wuser = '0;
        end
        if (ENABLE_POISON) begin
            m_axil_wpoison = w_w_rd_data[idx +: PW];
            idx += PW;
        end else begin
            m_axil_wpoison = '0;
        end
    end

    // ---------------------------------------------------------------------
    // B channel
    // ---------------------------------------------------------------------
    logic [BSize-1:0] w_b_wr_data, w_b_rd_data;
    logic [3:0]        w_b_count;

    always_comb begin
        automatic int idx = 0;
        w_b_wr_data[idx +: 2] = m_axil_bresp;
        idx += 2;
        if (ENABLE_USER) begin
            w_b_wr_data[idx +: UW] = m_axil_buser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_b_wr_data[idx +: 1] = m_axil_btrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_b_wr_data[idx +: LW] = m_axil_bloop;
            idx += LW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) b_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (m_axil_bvalid),
        .wr_ready    (m_axil_bready),
        .wr_data     (w_b_wr_data),
        .rd_valid    (fub_bvalid),
        .rd_ready    (fub_bready),
        .rd_count    (w_b_count),
        .rd_data     (w_b_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        fub_bresp = w_b_rd_data[idx +: 2];
        idx += 2;
        if (ENABLE_USER) begin
            fub_buser = w_b_rd_data[idx +: UW];
            idx += UW;
        end else begin
            fub_buser = '0;
        end
        if (ENABLE_TRACE) begin
            fub_btrace = w_b_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_btrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            fub_bloop = w_b_rd_data[idx +: LW];
            idx += LW;
        end else begin
            fub_bloop = '0;
        end
    end

    assign busy = (w_aw_count > 0) ||
                  (w_w_count > 0) ||
                  (w_b_count > 0);

endmodule : axil5_master_wr
