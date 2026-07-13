// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_wr_splitter
// Purpose: FSM-free write-side splitter. Chops the host AW burst into DFI-burst
//          sized sub-commands (via pumice_axi_burst_chopper) and re-frames the W
//          stream so each sub-command sees exactly one WLAST at its CHUNK_BEATS
//          boundary. This is the request-side transform only: the B channel is
//          NOT here - sub-burst B responses are consolidated to one host B by
//          pumice_wr_aggregator on the return path.
//
//          The WLAST re-frame is the key correctness point. It is driven purely
//          off the W handshake (a CHUNK_BEATS down-counter), NOT off the AW
//          side. The old shared axi_master_wr_splitter tied WLAST to a beat
//          budget set by its AW FSM, which desynced from the W stream when a
//          host burst split into many single-beat DRAM bursts (e.g. x16), so
//          most sub-bursts never got a WLAST and the write-data CAM never
//          delimited them. Counting the W stream directly makes the framing
//          exact for any CHUNK_BEATS, including 1.
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_wr_splitter #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,
    parameter int CHUNK_BEATS    = 1,   // AXI beats per DFI burst (power of 2)
    // Derived
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8
) (
    input  logic              aclk,
    input  logic              aresetn,

    // ---- host AW/W in ------------------------------------------------------
    input  logic [IW-1:0]     fub_awid,
    input  logic [AW-1:0]     fub_awaddr,
    input  logic [7:0]        fub_awlen,
    input  logic [2:0]        fub_awsize,
    input  logic [1:0]        fub_awburst,
    input  logic              fub_awlock,
    input  logic [3:0]        fub_awcache,
    input  logic [2:0]        fub_awprot,
    input  logic [3:0]        fub_awqos,
    input  logic [3:0]        fub_awregion,
    input  logic [UW-1:0]     fub_awuser,
    input  logic              fub_awvalid,
    output logic              fub_awready,
    input  logic [DW-1:0]     fub_wdata,
    input  logic [SW-1:0]     fub_wstrb,
    input  logic              fub_wlast,
    input  logic [UW-1:0]     fub_wuser,
    input  logic              fub_wvalid,
    output logic              fub_wready,

    // ---- sub-command AW/W out (to intake) ---------------------------------
    output logic [IW-1:0]     m_awid,
    output logic [AW-1:0]     m_awaddr,
    output logic [7:0]        m_awlen,
    output logic [2:0]        m_awsize,
    output logic [1:0]        m_awburst,
    output logic              m_awlock,
    output logic [3:0]        m_awcache,
    output logic [2:0]        m_awprot,
    output logic [3:0]        m_awqos,
    output logic [3:0]        m_awregion,
    output logic [UW-1:0]     m_awuser,
    output logic              m_awvalid,
    input  logic              m_awready,
    output logic [DW-1:0]     m_wdata,
    output logic [SW-1:0]     m_wstrb,
    output logic              m_wlast,
    output logic [UW-1:0]     m_wuser,
    output logic              m_wvalid,
    input  logic              m_wready,

    // ---- aggregation sideband (aligned with m_aw*) ------------------------
    output logic              m_aw_agg,   // sub-command is part of a split
    output logic              m_aw_last   // sub-command is the final one
);

    // ---- AW: burst chopper -------------------------------------------------
    pumice_axi_burst_chopper #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_USER_WIDTH(UW),
        .STRB_BYTES(SW), .CHUNK_BEATS(CHUNK_BEATS)
    ) u_aw_chop (
        .aclk(aclk), .aresetn(aresetn),
        .fub_axid(fub_awid), .fub_axaddr(fub_awaddr), .fub_axlen(fub_awlen),
        .fub_axsize(fub_awsize), .fub_axburst(fub_awburst), .fub_axlock(fub_awlock),
        .fub_axcache(fub_awcache), .fub_axprot(fub_awprot), .fub_axqos(fub_awqos),
        .fub_axregion(fub_awregion), .fub_axuser(fub_awuser),
        .fub_axvalid(fub_awvalid), .fub_axready(fub_awready),
        .m_axid(m_awid), .m_axaddr(m_awaddr), .m_axlen(m_awlen),
        .m_axsize(m_awsize), .m_axburst(m_awburst), .m_axlock(m_awlock),
        .m_axcache(m_awcache), .m_axprot(m_awprot), .m_axqos(m_awqos),
        .m_axregion(m_awregion), .m_axuser(m_awuser),
        .m_axvalid(m_awvalid), .m_axready(m_awready),
        .m_ax_agg(m_aw_agg), .m_ax_last(m_aw_last)
    );

    // ---- W: pass data through, regenerate WLAST every CHUNK_BEATS beats -----
    logic [8:0] r_wcnt;   // beats until the next re-framed WLAST (down-counter)
    logic       w_wacc;

    assign m_wdata  = fub_wdata;
    assign m_wstrb  = fub_wstrb;
    assign m_wuser  = fub_wuser;
    assign m_wvalid = fub_wvalid;
    assign fub_wready = m_wready;
    // WLAST at the CHUNK boundary; also honour the host's own final beat so a
    // ragged tail still closes cleanly.
    assign m_wlast  = fub_wlast || (r_wcnt == 9'd0);

    assign w_wacc = m_wvalid && m_wready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wcnt <= 9'(CHUNK_BEATS - 1);
        end else if (w_wacc) begin
            r_wcnt <= m_wlast ? 9'(CHUNK_BEATS - 1) : (r_wcnt - 9'd1);
        end
    )

endmodule : pumice_wr_splitter
