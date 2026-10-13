// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_wr
// Purpose: AXI5-Lite write slave transport
//
// AXI5-Lite transport (IHI 0022 Issue L, B2.1.5 and Table B2.2).
// Structurally this is axil4_slave_wr plus the AXI5-Lite transaction ID and the
// optional signal groups the spec allows on AXI5-Lite: USER, TRACE and
// POISON. Each group is gated by its own ENABLE_* parameter and contributes
// to the packed SKID payload only when enabled.
//
// The ID (AWID/BID, ARID/RID; ID_WIDTH bits) is mandatory on this
// Subordinate-side interface (Table B2.2, code YS), so ID_WIDTH is 1..32 here
// and the ID is always carried.
//
// AxLOCK, AxMPAM, AxMECID, AxNSAID and xLOOP are NOT carried: Table B2.2 marks
// them "not present" on AXI5-Lite, and exclusive accesses are not supported
// (B2.1.5). They were carried until issue #102.
//
// It transports; it does not interpret. The ID is carried in both directions
// like every other field, so a response leaves with the ID the Subordinate
// behind this module gave it -- reflecting AxID onto BID/RID is that
// Subordinate's job (A5.1.1). TRACE and USER are carried end to end
// unmodified. POISON is carried, never generated and never checked.
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

    // AXI5-Lite ID and optional signal widths
    // AWID/BID and ARID/RID width (IHI 0022L Table A5.2: 0..32).
    // This is a Subordinate-side interface, where Table B2.2 makes the ID
    // mandatory (code YS), so the legal range here is 1..32.
    parameter int ID_WIDTH           = 4,
    parameter int USER_WIDTH         = 4,

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW    = 2,
    parameter int SKID_DEPTH_W     = 4,
    parameter int SKID_DEPTH_B     = 2,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int SW       = DW / 8,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int AWSize = AW + 3 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0),

    parameter int WSize  = DW + SW +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_POISON ? PW : 0),

    parameter int BSize  = 2 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AW channel: s_axil_ -> fub_
    input  logic [IW-1:0]           s_axil_awid,
    input  logic [AW-1:0]           s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic [UW-1:0]           s_axil_awuser,
    input  logic                    s_axil_awtrace,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    output logic [IW-1:0]           fub_awid,
    output logic [AW-1:0]           fub_awaddr,
    output logic [2:0]              fub_awprot,
    output logic [UW-1:0]           fub_awuser,
    output logic                    fub_awtrace,
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
    input  logic [IW-1:0]           fub_bid,
    input  logic [1:0]              fub_bresp,
    input  logic [UW-1:0]           fub_buser,
    input  logic                    fub_btrace,
    input  logic                    fub_bvalid,
    output logic                    fub_bready,
    output logic [IW-1:0]           s_axil_bid,
    output logic [1:0]              s_axil_bresp,
    output logic [UW-1:0]           s_axil_buser,
    output logic                    s_axil_btrace,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,

    // Status output for clock gating
    output logic                       busy
);

    // ---------------------------------------------------------------------
    // Elaboration-time parameter guard (the one sanctioned in-RTL check; see
    // vault/handbook/design/no-assertions-in-rtl.md). Checks nothing at run
    // time.
    //   AXIL_DATA_WIDTH: AXI5-Lite takes any AXI DATA_WIDTH -- 8, 16, 32, 64,
    //     128, 256, 512 or 1024 (IHI 0022L Table A3.19; Table B2.4 adds no
    //     AXI5-Lite constraint, unlike AXI4-Lite's 32/64 of IHI 0022H B1.1.2).
    //   ID_WIDTH: 1..32 (Table A5.2). Subordinate-side: the ID is mandatory (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_slave_wr: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 1 || ID_WIDTH > 32)
            $fatal(1, "axil5_slave_wr: ID_WIDTH=%0d out of range 1..32 (IHI 0022L Table A5.2; a Subordinate must carry the ID)",
                   ID_WIDTH);
    end
`endif

    // ---------------------------------------------------------------------
    // AW channel
    // ---------------------------------------------------------------------
    logic [AWSize-1:0] w_aw_wr_data, w_aw_rd_data;
    logic [3:0]        w_aw_count;

    always_comb begin
        automatic int idx = 0;
        if (ID_WIDTH > 0) begin
            w_aw_wr_data[idx +: IW] = s_axil_awid;
            idx += IW;
        end
        w_aw_wr_data[idx +: AW] = s_axil_awaddr;
        idx += AW;
        w_aw_wr_data[idx +: 3] = s_axil_awprot;
        idx += 3;
        if (ENABLE_USER) begin
            w_aw_wr_data[idx +: UW] = s_axil_awuser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_aw_wr_data[idx +: 1] = s_axil_awtrace;
            idx += 1;
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
        if (ID_WIDTH > 0) begin
            fub_awid = w_aw_rd_data[idx +: IW];
            idx += IW;
        end else begin
            fub_awid = '0;
        end
        fub_awaddr = w_aw_rd_data[idx +: AW];
        idx += AW;
        fub_awprot = w_aw_rd_data[idx +: 3];
        idx += 3;
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
        if (ID_WIDTH > 0) begin
            w_b_wr_data[idx +: IW] = fub_bid;
            idx += IW;
        end
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
        if (ID_WIDTH > 0) begin
            s_axil_bid = w_b_rd_data[idx +: IW];
            idx += IW;
        end else begin
            s_axil_bid = '0;
        end
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
    end

    assign busy = (w_aw_count > 0) ||
                  (w_w_count > 0) ||
                  (w_b_count > 0) ||
                  s_axil_awvalid || s_axil_wvalid || fub_bvalid;

endmodule : axil5_slave_wr
