// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_rd
// Purpose: AXI5-Lite read master transport
//
// AXI5-Lite transport. Structurally this is axil4_master_rd with the AXI5-Lite optional
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

module axil5_master_rd
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
    parameter int SKID_DEPTH_AR    = 2,
    parameter int SKID_DEPTH_R     = 4,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int ARSize = AW + 3 +
                             (ENABLE_LOCK ? 1 : 0) +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_MPAM ? MW : 0) +
                             (ENABLE_MECID ? EW : 0) +
                             (ENABLE_NSAID ? NW : 0),

    parameter int RSize  = DW + 2 +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_POISON ? PW : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AR channel: fub_ -> m_axil_
    input  logic [AW-1:0]           fub_araddr,
    input  logic [2:0]              fub_arprot,
    input  logic                    fub_arlock,
    input  logic [UW-1:0]           fub_aruser,
    input  logic                    fub_artrace,
    input  logic [LW-1:0]           fub_arloop,
    input  logic [MW-1:0]           fub_armpam,
    input  logic [EW-1:0]           fub_armecid,
    input  logic [NW-1:0]           fub_arnsaid,
    input  logic                    fub_arvalid,
    output logic                    fub_arready,
    output logic [AW-1:0]           m_axil_araddr,
    output logic [2:0]              m_axil_arprot,
    output logic                    m_axil_arlock,
    output logic [UW-1:0]           m_axil_aruser,
    output logic                    m_axil_artrace,
    output logic [LW-1:0]           m_axil_arloop,
    output logic [MW-1:0]           m_axil_armpam,
    output logic [EW-1:0]           m_axil_armecid,
    output logic [NW-1:0]           m_axil_arnsaid,
    output logic                    m_axil_arvalid,
    input  logic                    m_axil_arready,

    // R channel: m_axil_ -> fub_
    input  logic [DW-1:0]           m_axil_rdata,
    input  logic [1:0]              m_axil_rresp,
    input  logic [UW-1:0]           m_axil_ruser,
    input  logic                    m_axil_rtrace,
    input  logic [LW-1:0]           m_axil_rloop,
    input  logic [PW-1:0]           m_axil_rpoison,
    input  logic                    m_axil_rvalid,
    output logic                    m_axil_rready,
    output logic [DW-1:0]           fub_rdata,
    output logic [1:0]              fub_rresp,
    output logic [UW-1:0]           fub_ruser,
    output logic                    fub_rtrace,
    output logic [LW-1:0]           fub_rloop,
    output logic [PW-1:0]           fub_rpoison,
    output logic                    fub_rvalid,
    input  logic                    fub_rready,

    // Status output for clock gating
    output logic                       busy
);

    // ---------------------------------------------------------------------
    // AR channel
    // ---------------------------------------------------------------------
    logic [ARSize-1:0] w_ar_wr_data, w_ar_rd_data;
    logic [3:0]        w_ar_count;

    always_comb begin
        automatic int idx = 0;
        w_ar_wr_data[idx +: AW] = fub_araddr;
        idx += AW;
        w_ar_wr_data[idx +: 3] = fub_arprot;
        idx += 3;
        if (ENABLE_LOCK) begin
            w_ar_wr_data[idx +: 1] = fub_arlock;
            idx += 1;
        end
        if (ENABLE_USER) begin
            w_ar_wr_data[idx +: UW] = fub_aruser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_ar_wr_data[idx +: 1] = fub_artrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_ar_wr_data[idx +: LW] = fub_arloop;
            idx += LW;
        end
        if (ENABLE_MPAM) begin
            w_ar_wr_data[idx +: MW] = fub_armpam;
            idx += MW;
        end
        if (ENABLE_MECID) begin
            w_ar_wr_data[idx +: EW] = fub_armecid;
            idx += EW;
        end
        if (ENABLE_NSAID) begin
            w_ar_wr_data[idx +: NW] = fub_arnsaid;
            idx += NW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) ar_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_arvalid),
        .wr_ready    (fub_arready),
        .wr_data     (w_ar_wr_data),
        .rd_valid    (m_axil_arvalid),
        .rd_ready    (m_axil_arready),
        .rd_count    (w_ar_count),
        .rd_data     (w_ar_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        m_axil_araddr = w_ar_rd_data[idx +: AW];
        idx += AW;
        m_axil_arprot = w_ar_rd_data[idx +: 3];
        idx += 3;
        if (ENABLE_LOCK) begin
            m_axil_arlock = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axil_arlock = 1'b0;
        end
        if (ENABLE_USER) begin
            m_axil_aruser = w_ar_rd_data[idx +: UW];
            idx += UW;
        end else begin
            m_axil_aruser = '0;
        end
        if (ENABLE_TRACE) begin
            m_axil_artrace = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axil_artrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            m_axil_arloop = w_ar_rd_data[idx +: LW];
            idx += LW;
        end else begin
            m_axil_arloop = '0;
        end
        if (ENABLE_MPAM) begin
            m_axil_armpam = w_ar_rd_data[idx +: MW];
            idx += MW;
        end else begin
            m_axil_armpam = '0;
        end
        if (ENABLE_MECID) begin
            m_axil_armecid = w_ar_rd_data[idx +: EW];
            idx += EW;
        end else begin
            m_axil_armecid = '0;
        end
        if (ENABLE_NSAID) begin
            m_axil_arnsaid = w_ar_rd_data[idx +: NW];
            idx += NW;
        end else begin
            m_axil_arnsaid = '0;
        end
    end

    // ---------------------------------------------------------------------
    // R channel
    // ---------------------------------------------------------------------
    logic [RSize-1:0] w_r_wr_data, w_r_rd_data;
    logic [3:0]        w_r_count;

    always_comb begin
        automatic int idx = 0;
        w_r_wr_data[idx +: DW] = m_axil_rdata;
        idx += DW;
        w_r_wr_data[idx +: 2] = m_axil_rresp;
        idx += 2;
        if (ENABLE_USER) begin
            w_r_wr_data[idx +: UW] = m_axil_ruser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_r_wr_data[idx +: 1] = m_axil_rtrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_r_wr_data[idx +: LW] = m_axil_rloop;
            idx += LW;
        end
        if (ENABLE_POISON) begin
            w_r_wr_data[idx +: PW] = m_axil_rpoison;
            idx += PW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) r_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (m_axil_rvalid),
        .wr_ready    (m_axil_rready),
        .wr_data     (w_r_wr_data),
        .rd_valid    (fub_rvalid),
        .rd_ready    (fub_rready),
        .rd_count    (w_r_count),
        .rd_data     (w_r_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        fub_rdata = w_r_rd_data[idx +: DW];
        idx += DW;
        fub_rresp = w_r_rd_data[idx +: 2];
        idx += 2;
        if (ENABLE_USER) begin
            fub_ruser = w_r_rd_data[idx +: UW];
            idx += UW;
        end else begin
            fub_ruser = '0;
        end
        if (ENABLE_TRACE) begin
            fub_rtrace = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_rtrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            fub_rloop = w_r_rd_data[idx +: LW];
            idx += LW;
        end else begin
            fub_rloop = '0;
        end
        if (ENABLE_POISON) begin
            fub_rpoison = w_r_rd_data[idx +: PW];
            idx += PW;
        end else begin
            fub_rpoison = '0;
        end
    end

    assign busy = (w_ar_count > 0) ||
                  (w_r_count > 0);

endmodule : axil5_master_rd
