// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_rd
// Purpose: AXI5-Lite read master transport
//
// AXI5-Lite transport (IHI 0022 Issue L, B2.1.5 and Table B2.2).
// Structurally this is axil4_master_rd plus the AXI5-Lite transaction ID and the
// optional signal groups the spec allows on AXI5-Lite: USER, TRACE and
// POISON. Each group is gated by its own ENABLE_* parameter and contributes
// to the packed SKID payload only when enabled.
//
// The ID (AWID/BID, ARID/RID; ID_WIDTH bits) is optional on this Manager-side
// interface (Table B2.2, code YS). With ID_WIDTH = 0 the m_axil_ ID outputs
// are driven 0 and the ID inputs are ignored, and a build with ID_WIDTH = 0
// and every group disabled has the same payload width and the same behaviour
// as the AXI4-Lite module of the same name -- which is the property
// val/amba/test_axil5_axil4_equivalence.py relies on.
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

module axil5_master_rd
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

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR    = 2,
    parameter int SKID_DEPTH_R     = 4,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int ARSize = AW + 3 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0),

    parameter int RSize  = DW + 2 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_POISON ? PW : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AR channel: fub_ -> m_axil_
    input  logic [IW-1:0]           fub_arid,
    input  logic [AW-1:0]           fub_araddr,
    input  logic [2:0]              fub_arprot,
    input  logic [UW-1:0]           fub_aruser,
    input  logic                    fub_artrace,
    input  logic                    fub_arvalid,
    output logic                    fub_arready,
    output logic [IW-1:0]           m_axil_arid,
    output logic [AW-1:0]           m_axil_araddr,
    output logic [2:0]              m_axil_arprot,
    output logic [UW-1:0]           m_axil_aruser,
    output logic                    m_axil_artrace,
    output logic                    m_axil_arvalid,
    input  logic                    m_axil_arready,

    // R channel: m_axil_ -> fub_
    input  logic [IW-1:0]           m_axil_rid,
    input  logic [DW-1:0]           m_axil_rdata,
    input  logic [1:0]              m_axil_rresp,
    input  logic [UW-1:0]           m_axil_ruser,
    input  logic                    m_axil_rtrace,
    input  logic [PW-1:0]           m_axil_rpoison,
    input  logic                    m_axil_rvalid,
    output logic                    m_axil_rready,
    output logic [IW-1:0]           fub_rid,
    output logic [DW-1:0]           fub_rdata,
    output logic [1:0]              fub_rresp,
    output logic [UW-1:0]           fub_ruser,
    output logic                    fub_rtrace,
    output logic [PW-1:0]           fub_rpoison,
    output logic                    fub_rvalid,
    input  logic                    fub_rready,

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
    //   ID_WIDTH: 0..32 (Table A5.2). Manager-side: 0 = no ID is legal (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_master_rd: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 0 || ID_WIDTH > 32)
            $fatal(1, "axil5_master_rd: ID_WIDTH=%0d out of range 0..32 (IHI 0022L Table A5.2)",
                   ID_WIDTH);
    end
`endif

    // ---------------------------------------------------------------------
    // AR channel
    // ---------------------------------------------------------------------
    logic [ARSize-1:0] w_ar_wr_data, w_ar_rd_data;
    logic [3:0]        w_ar_count;

    always_comb begin
        automatic int idx = 0;
        if (ID_WIDTH > 0) begin
            w_ar_wr_data[idx +: IW] = fub_arid;
            idx += IW;
        end
        w_ar_wr_data[idx +: AW] = fub_araddr;
        idx += AW;
        w_ar_wr_data[idx +: 3] = fub_arprot;
        idx += 3;
        if (ENABLE_USER) begin
            w_ar_wr_data[idx +: UW] = fub_aruser;
            idx += UW;
        end
        if (ENABLE_TRACE) begin
            w_ar_wr_data[idx +: 1] = fub_artrace;
            idx += 1;
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
        if (ID_WIDTH > 0) begin
            m_axil_arid = w_ar_rd_data[idx +: IW];
            idx += IW;
        end else begin
            m_axil_arid = '0;
        end
        m_axil_araddr = w_ar_rd_data[idx +: AW];
        idx += AW;
        m_axil_arprot = w_ar_rd_data[idx +: 3];
        idx += 3;
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
    end

    // ---------------------------------------------------------------------
    // R channel
    // ---------------------------------------------------------------------
    logic [RSize-1:0] w_r_wr_data, w_r_rd_data;
    logic [3:0]        w_r_count;

    always_comb begin
        automatic int idx = 0;
        if (ID_WIDTH > 0) begin
            w_r_wr_data[idx +: IW] = m_axil_rid;
            idx += IW;
        end
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
        if (ID_WIDTH > 0) begin
            fub_rid = w_r_rd_data[idx +: IW];
            idx += IW;
        end else begin
            fub_rid = '0;
        end
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
