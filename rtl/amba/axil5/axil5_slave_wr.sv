// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_wr
// Purpose: AXI5-Lite write slave transport
//
// AXI5-Lite transport. Structurally this is axil4_slave_wr with the AXI5-Lite optional
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

module axil5_slave_wr
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

    // AW channel: s_axil_ -> fub_
    input  logic [AW-1:0]           s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic                    s_axil_awlock,
    input  logic [UW-1:0]           s_axil_awuser,
    input  logic                    s_axil_awtrace,
    input  logic [LW-1:0]           s_axil_awloop,
    input  logic [MW-1:0]           s_axil_awmpam,
    input  logic [EW-1:0]           s_axil_awmecid,
    input  logic [NW-1:0]           s_axil_awnsaid,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    output logic [AW-1:0]           fub_awaddr,
    output logic [2:0]              fub_awprot,
    output logic                    fub_awlock,
    output logic [UW-1:0]           fub_awuser,
    output logic                    fub_awtrace,
    output logic [LW-1:0]           fub_awloop,
    output logic [MW-1:0]           fub_awmpam,
    output logic [EW-1:0]           fub_awmecid,
    output logic [NW-1:0]           fub_awnsaid,
    output logic                    fub_awvalid,
    input  logic                    fub_awready,

    // W channel: s_axil_ -> fub_
    input  logic [DW-1:0]           s_axil_wdata,
    input  logic [SW-1:0]           s_axil_wstrb,
    input  logic [UW-1:0]           s_axil_wuser,
    input  logic [PW-1:0]           s_axil_wpoison,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [DW-1:0]           fub_wdata,
    output logic [SW-1:0]           fub_wstrb,
    output logic [UW-1:0]           fub_wuser,
    output logic [PW-1:0]           fub_wpoison,
    output logic                    fub_wvalid,
    input  logic                    fub_wready,

    // B channel: fub_ -> s_axil_
    input  logic [1:0]              fub_bresp,
    input  logic [UW-1:0]           fub_buser,
    input  logic                    fub_btrace,
    input  logic [LW-1:0]           fub_bloop,
    input  logic                    fub_bvalid,
    output logic                    fub_bready,
    output logic [1:0]              s_axil_bresp,
    output logic [UW-1:0]           s_axil_buser,
    output logic                    s_axil_btrace,
    output logic [LW-1:0]           s_axil_bloop,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,

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
        w_aw_wr_data[idx +: AW] = s_axil_awaddr;
        idx += AW;
        w_aw_wr_data[idx +: 3] = s_axil_awprot;
        idx += 3;
        if (ENABLE_LOCK) begin
            w_aw_wr_data[idx +: 1] = s_axil_awlock;
            idx += 1;
        end
        if (ENABLE_USER) begin
            w_aw_wr_data[idx +: UW] = s_axil_awuser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_aw_wr_data[idx +: 1] = s_axil_awtrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_aw_wr_data[idx +: LW] = s_axil_awloop;
            idx += LW;
        end
        if (ENABLE_MPAM) begin
            w_aw_wr_data[idx +: MW] = s_axil_awmpam;
            idx += MW;
        end
        if (ENABLE_MECID) begin
            w_aw_wr_data[idx +: EW] = s_axil_awmecid;
            idx += EW;
        end
        if (ENABLE_NSAID) begin
            w_aw_wr_data[idx +: NW] = s_axil_awnsaid;
            idx += NW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) aw_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (s_axil_awvalid),
        .wr_ready    (s_axil_awready),
        .wr_data     (w_aw_wr_data),
        .rd_valid    (fub_awvalid),
        .rd_ready    (fub_awready),
        .rd_count    (w_aw_count),
        .rd_data     (w_aw_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        fub_awaddr = w_aw_rd_data[idx +: AW];
        idx += AW;
        fub_awprot = w_aw_rd_data[idx +: 3];
        idx += 3;
        if (ENABLE_LOCK) begin
            fub_awlock = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_awlock = 1'b0;
        end
        if (ENABLE_USER) begin
            fub_awuser = w_aw_rd_data[idx +: UW];
            idx += UW;
        end else begin
            fub_awuser = '0;
        end
        if (ENABLE_TRACE) begin
            fub_awtrace = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_awtrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            fub_awloop = w_aw_rd_data[idx +: LW];
            idx += LW;
        end else begin
            fub_awloop = '0;
        end
        if (ENABLE_MPAM) begin
            fub_awmpam = w_aw_rd_data[idx +: MW];
            idx += MW;
        end else begin
            fub_awmpam = '0;
        end
        if (ENABLE_MECID) begin
            fub_awmecid = w_aw_rd_data[idx +: EW];
            idx += EW;
        end else begin
            fub_awmecid = '0;
        end
        if (ENABLE_NSAID) begin
            fub_awnsaid = w_aw_rd_data[idx +: NW];
            idx += NW;
        end else begin
            fub_awnsaid = '0;
        end
    end

    // ---------------------------------------------------------------------
    // W channel
    // ---------------------------------------------------------------------
    logic [WSize-1:0] w_w_wr_data, w_w_rd_data;
    logic [3:0]        w_w_count;

    always_comb begin
        automatic int idx = 0;
        w_w_wr_data[idx +: DW] = s_axil_wdata;
        idx += DW;
        w_w_wr_data[idx +: SW] = s_axil_wstrb;
        idx += SW;
        if (ENABLE_USER) begin
            w_w_wr_data[idx +: UW] = s_axil_wuser;
            idx += UW;
        end
        if (ENABLE_POISON) begin
            w_w_wr_data[idx +: PW] = s_axil_wpoison;
            idx += PW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) w_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (s_axil_wvalid),
        .wr_ready    (s_axil_wready),
        .wr_data     (w_w_wr_data),
        .rd_valid    (fub_wvalid),
        .rd_ready    (fub_wready),
        .rd_count    (w_w_count),
        .rd_data     (w_w_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        fub_wdata = w_w_rd_data[idx +: DW];
        idx += DW;
        fub_wstrb = w_w_rd_data[idx +: SW];
        idx += SW;
        if (ENABLE_USER) begin
            fub_wuser = w_w_rd_data[idx +: UW];
            idx += UW;
        end else begin
            fub_wuser = '0;
        end
        if (ENABLE_POISON) begin
            fub_wpoison = w_w_rd_data[idx +: PW];
            idx += PW;
        end else begin
            fub_wpoison = '0;
        end
    end

    // ---------------------------------------------------------------------
    // B channel
    // ---------------------------------------------------------------------
    logic [BSize-1:0] w_b_wr_data, w_b_rd_data;
    logic [3:0]        w_b_count;

    always_comb begin
        automatic int idx = 0;
        w_b_wr_data[idx +: 2] = fub_bresp;
        idx += 2;
        if (ENABLE_USER) begin
            w_b_wr_data[idx +: UW] = fub_buser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_b_wr_data[idx +: 1] = fub_btrace;
            idx += 1;
        end
        if (ENABLE_LOOP) begin
            w_b_wr_data[idx +: LW] = fub_bloop;
            idx += LW;
        end
    end

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) b_channel (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_bvalid),
        .wr_ready    (fub_bready),
        .wr_data     (w_b_wr_data),
        .rd_valid    (s_axil_bvalid),
        .rd_ready    (s_axil_bready),
        .rd_count    (w_b_count),
        .rd_data     (w_b_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    always_comb begin
        automatic int idx = 0;
        s_axil_bresp = w_b_rd_data[idx +: 2];
        idx += 2;
        if (ENABLE_USER) begin
            s_axil_buser = w_b_rd_data[idx +: UW];
            idx += UW;
        end else begin
            s_axil_buser = '0;
        end
        if (ENABLE_TRACE) begin
            s_axil_btrace = w_b_rd_data[idx +: 1];
            idx += 1;
        end else begin
            s_axil_btrace = 1'b0;
        end
        if (ENABLE_LOOP) begin
            s_axil_bloop = w_b_rd_data[idx +: LW];
            idx += LW;
        end else begin
            s_axil_bloop = '0;
        end
    end

    assign busy = (w_aw_count > 0) ||
                  (w_w_count > 0) ||
                  (w_b_count > 0);

endmodule : axil5_slave_wr
