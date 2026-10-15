// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: fb_endpoints
// Purpose: The fabric benchmark's LFSR source (S2) and CRC sink (S3) on their
//          own clock, behind CDC crossings, with their verdicts brought back.
//
// Documentation: projects/fpga-systems/Genesys2/fabric-benchmark/PRD.md
//                (DE10 PRD sections 4.1 and 5.3: fabric-only mode, clocks)
//
// Author: sean galloway
// Created: 2026-10-14
//
//==============================================================================
// Description:
//   Two slave ports on the FABRIC clock (aclk): s_rd_* is the LFSR source
//   window, s_wr_* the CRC sink window. Each crosses into the ENDPOINT clock
//   (ep_clk) through its own axi4_cdc_{rd,wr}, where one axi4_dma_slaves --
//   the same source/sink the Genesys 2 STREAM harness uses -- answers both.
//   Nothing here knows which fabric is upstream; both legs see this block
//   unchanged.
//
//   Why a separate clock: the endpoints accept a beat every cycle, and on a
//   clock at least as fast as the fabric's they cannot be what limits a run.
//   The slave-side observers sit on the s_* ports, upstream of the crossings,
//   so the crossings and endpoints fall out of the fabric's measured latency.
//
//   Status back to aclk. The CRCs and beat counts live in ep_clk. They return
//   as ONE coherent snapshot through cdc_2_phase_handshake, resent
//   continuously: the aclk side only ever sees a complete bundle, never a mix
//   of an old CRC and a new count. The cost is a lag of a few cycles of both
//   clocks per update -- identical in every leg, and outside the measurement
//   (the observers do the timing; the harness timer only stops the run).
//
//   The clear pulse goes the other way through sync_pulse. A clear issued
//   while beats are in flight is the host's error, as in the STREAM harness.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   NUM_CHANNELS   - STREAM channels; binned on the low ID bits (1..8)
//   AXI_ID_WIDTH   - slave-side ID width ({fabric slot, master id})
//   AXI_DATA_WIDTH - fabric data width
//   CDC_DEPTH      - async FIFO depth per AXI channel; 16 sustains a beat per
//                    cycle with the synchronizer round trip in flight
//   LFSR_SEED      - source seed (channel N uses LFSR_SEED ^ N); identical in
//                    every leg -- the legs are compared on the same data
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   axi4_dma_slaves, axi4_cdc_rd, axi4_cdc_wr, cdc_2_phase_handshake, sync_pulse
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_endpoints #(
    parameter int          NUM_CHANNELS   = 8,
    parameter int          AXI_ID_WIDTH   = 10,
    parameter int          AXI_ADDR_WIDTH = 32,
    parameter int          AXI_DATA_WIDTH = 128,
    parameter int          CDC_DEPTH      = 16,
    parameter logic [31:0] LFSR_SEED      = 32'hDEADBEEF,
    // Short params
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int SW = DW / 8,
    parameter int NC = NUM_CHANNELS
) (
    // Fabric clock: the slave ports and every status output
    input  logic              aclk,
    input  logic              aresetn,
    // Endpoint clock
    input  logic              ep_clk,
    input  logic              ep_aresetn,

    // Clear both CRCs and beat counts (aclk pulse)
    input  logic              i_clear,

    // S2: LFSR source (read only)
    input  logic [IW-1:0]     s_rd_arid,
    input  logic [AW-1:0]     s_rd_araddr,
    input  logic [7:0]        s_rd_arlen,
    input  logic [2:0]        s_rd_arsize,
    input  logic [1:0]        s_rd_arburst,
    input  logic              s_rd_arlock,
    input  logic [3:0]        s_rd_arcache,
    input  logic [2:0]        s_rd_arprot,
    input  logic [3:0]        s_rd_arqos,
    input  logic              s_rd_arvalid,
    output logic              s_rd_arready,
    output logic [IW-1:0]     s_rd_rid,
    output logic [DW-1:0]     s_rd_rdata,
    output logic [1:0]        s_rd_rresp,
    output logic              s_rd_rlast,
    output logic              s_rd_rvalid,
    input  logic              s_rd_rready,

    // S3: CRC sink (write only)
    input  logic [IW-1:0]     s_wr_awid,
    input  logic [AW-1:0]     s_wr_awaddr,
    input  logic [7:0]        s_wr_awlen,
    input  logic [2:0]        s_wr_awsize,
    input  logic [1:0]        s_wr_awburst,
    input  logic              s_wr_awlock,
    input  logic [3:0]        s_wr_awcache,
    input  logic [2:0]        s_wr_awprot,
    input  logic [3:0]        s_wr_awqos,
    input  logic              s_wr_awvalid,
    output logic              s_wr_awready,
    input  logic [DW-1:0]     s_wr_wdata,
    input  logic [SW-1:0]     s_wr_wstrb,
    input  logic              s_wr_wlast,
    input  logic              s_wr_wvalid,
    output logic              s_wr_wready,
    output logic [IW-1:0]     s_wr_bid,
    output logic [1:0]        s_wr_bresp,
    output logic              s_wr_bvalid,
    input  logic              s_wr_bready,

    // Verdicts, aclk domain (one coherent snapshot, refreshed continuously)
    output logic [NC-1:0][31:0] o_read_crc_value,
    output logic [NC-1:0]       o_read_crc_valid,
    output logic [31:0]         o_read_beat_count,
    output logic [NC-1:0][31:0] o_write_crc_value,
    output logic [NC-1:0]       o_write_crc_valid,
    output logic [31:0]         o_write_beat_count
);

    // ------------------------------------------------------------------------
    // Crossings into ep_clk. The CDCs carry USER/REGION; the port set has
    // neither, so they ride as zero.
    // ------------------------------------------------------------------------
    logic [IW-1:0] e_arid, e_rid, e_awid, e_bid;
    logic [AW-1:0] e_araddr, e_awaddr;
    logic [7:0]    e_arlen, e_awlen;
    logic [2:0]    e_arsize, e_awsize, e_arprot, e_awprot;
    logic [1:0]    e_arburst, e_awburst, e_rresp, e_bresp;
    logic          e_arlock, e_awlock;
    logic [3:0]    e_arcache, e_awcache, e_arqos, e_awqos, e_arregion, e_awregion;
    logic          e_aruser, e_ruser, e_awuser, e_wuser, e_buser;
    logic          e_arvalid, e_arready, e_rvalid, e_rready, e_rlast;
    logic [DW-1:0] e_rdata, e_wdata;
    logic [SW-1:0] e_wstrb;
    logic          e_awvalid, e_awready, e_wvalid, e_wready, e_wlast, e_bvalid, e_bready;

    axi4_cdc_rd #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(1), .CDC_DEPTH(CDC_DEPTH)
    ) u_cdc_rd (
        .s_aclk(aclk), .s_aresetn(aresetn),
        .s_axi_arid(s_rd_arid), .s_axi_araddr(s_rd_araddr), .s_axi_arlen(s_rd_arlen),
        .s_axi_arsize(s_rd_arsize), .s_axi_arburst(s_rd_arburst), .s_axi_arlock(s_rd_arlock),
        .s_axi_arcache(s_rd_arcache), .s_axi_arprot(s_rd_arprot), .s_axi_arqos(s_rd_arqos),
        .s_axi_arregion(4'b0), .s_axi_aruser(1'b0),
        .s_axi_arvalid(s_rd_arvalid), .s_axi_arready(s_rd_arready),
        .s_axi_rid(s_rd_rid), .s_axi_rdata(s_rd_rdata), .s_axi_rresp(s_rd_rresp),
        .s_axi_rlast(s_rd_rlast), .s_axi_ruser(), .s_axi_rvalid(s_rd_rvalid),
        .s_axi_rready(s_rd_rready),
        .m_aclk(ep_clk), .m_aresetn(ep_aresetn),
        .m_axi_arid(e_arid), .m_axi_araddr(e_araddr), .m_axi_arlen(e_arlen),
        .m_axi_arsize(e_arsize), .m_axi_arburst(e_arburst), .m_axi_arlock(e_arlock),
        .m_axi_arcache(e_arcache), .m_axi_arprot(e_arprot), .m_axi_arqos(e_arqos),
        .m_axi_arregion(e_arregion), .m_axi_aruser(e_aruser),
        .m_axi_arvalid(e_arvalid), .m_axi_arready(e_arready),
        .m_axi_rid(e_rid), .m_axi_rdata(e_rdata), .m_axi_rresp(e_rresp),
        .m_axi_rlast(e_rlast), .m_axi_ruser(e_ruser), .m_axi_rvalid(e_rvalid),
        .m_axi_rready(e_rready)
    );

    axi4_cdc_wr #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(1), .CDC_DEPTH(CDC_DEPTH)
    ) u_cdc_wr (
        .s_aclk(aclk), .s_aresetn(aresetn),
        .s_axi_awid(s_wr_awid), .s_axi_awaddr(s_wr_awaddr), .s_axi_awlen(s_wr_awlen),
        .s_axi_awsize(s_wr_awsize), .s_axi_awburst(s_wr_awburst), .s_axi_awlock(s_wr_awlock),
        .s_axi_awcache(s_wr_awcache), .s_axi_awprot(s_wr_awprot), .s_axi_awqos(s_wr_awqos),
        .s_axi_awregion(4'b0), .s_axi_awuser(1'b0),
        .s_axi_awvalid(s_wr_awvalid), .s_axi_awready(s_wr_awready),
        .s_axi_wdata(s_wr_wdata), .s_axi_wstrb(s_wr_wstrb), .s_axi_wlast(s_wr_wlast),
        .s_axi_wuser(1'b0), .s_axi_wvalid(s_wr_wvalid), .s_axi_wready(s_wr_wready),
        .s_axi_bid(s_wr_bid), .s_axi_bresp(s_wr_bresp), .s_axi_buser(),
        .s_axi_bvalid(s_wr_bvalid), .s_axi_bready(s_wr_bready),
        .m_aclk(ep_clk), .m_aresetn(ep_aresetn),
        .m_axi_awid(e_awid), .m_axi_awaddr(e_awaddr), .m_axi_awlen(e_awlen),
        .m_axi_awsize(e_awsize), .m_axi_awburst(e_awburst), .m_axi_awlock(e_awlock),
        .m_axi_awcache(e_awcache), .m_axi_awprot(e_awprot), .m_axi_awqos(e_awqos),
        .m_axi_awregion(e_awregion), .m_axi_awuser(e_awuser),
        .m_axi_awvalid(e_awvalid), .m_axi_awready(e_awready),
        .m_axi_wdata(e_wdata), .m_axi_wstrb(e_wstrb), .m_axi_wlast(e_wlast),
        .m_axi_wuser(e_wuser), .m_axi_wvalid(e_wvalid), .m_axi_wready(e_wready),
        .m_axi_bid(e_bid), .m_axi_bresp(e_bresp), .m_axi_buser(e_buser),
        .m_axi_bvalid(e_bvalid), .m_axi_bready(e_bready)
    );

    // ------------------------------------------------------------------------
    // Clear into ep_clk
    // ------------------------------------------------------------------------
    logic w_ep_clear;
    sync_pulse u_clear_sync (
        .i_src_clk(aclk),   .i_src_rst_n(aresetn), .i_pulse(i_clear),
        .i_dst_clk(ep_clk), .i_dst_rst_n(ep_aresetn), .o_pulse(w_ep_clear)
    );

    // ------------------------------------------------------------------------
    // The source and sink, in ep_clk
    // ------------------------------------------------------------------------
    logic [NC-1:0][31:0] w_rd_crc, w_wr_crc;
    logic [NC-1:0]       w_rd_crc_v, w_wr_crc_v;
    logic [31:0]         w_rd_beats, w_wr_beats;

    axi4_dma_slaves #(
        .NUM_CHANNELS(NC), .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(1), .LFSR_SEED(LFSR_SEED)
    ) u_slaves (
        .aclk(ep_clk), .aresetn(ep_aresetn),
        .read_lfsr_reset(w_ep_clear), .write_crc_reset(w_ep_clear),
        .read_crc_value(w_rd_crc), .read_crc_valid(w_rd_crc_v),
        .read_beat_count(), .read_beat_count_total(w_rd_beats),
        .write_crc_value(w_wr_crc), .write_crc_valid(w_wr_crc_v),
        .write_beat_count(), .write_beat_count_total(w_wr_beats),
        .s_axi_arid(e_arid), .s_axi_araddr(e_araddr), .s_axi_arlen(e_arlen),
        .s_axi_arsize(e_arsize), .s_axi_arburst(e_arburst), .s_axi_arlock(e_arlock),
        .s_axi_arcache(e_arcache), .s_axi_arprot(e_arprot), .s_axi_arqos(e_arqos),
        .s_axi_arregion(e_arregion), .s_axi_aruser(e_aruser),
        .s_axi_arvalid(e_arvalid), .s_axi_arready(e_arready),
        .s_axi_rid(e_rid), .s_axi_rdata(e_rdata), .s_axi_rresp(e_rresp),
        .s_axi_rlast(e_rlast), .s_axi_ruser(e_ruser), .s_axi_rvalid(e_rvalid),
        .s_axi_rready(e_rready),
        .s_axi_awid(e_awid), .s_axi_awaddr(e_awaddr), .s_axi_awlen(e_awlen),
        .s_axi_awsize(e_awsize), .s_axi_awburst(e_awburst), .s_axi_awlock(e_awlock),
        .s_axi_awcache(e_awcache), .s_axi_awprot(e_awprot), .s_axi_awqos(e_awqos),
        .s_axi_awregion(e_awregion), .s_axi_awuser(e_awuser),
        .s_axi_awvalid(e_awvalid), .s_axi_awready(e_awready),
        .s_axi_wdata(e_wdata), .s_axi_wstrb(e_wstrb), .s_axi_wlast(e_wlast),
        .s_axi_wuser(e_wuser), .s_axi_wvalid(e_wvalid), .s_axi_wready(e_wready),
        .s_axi_bid(e_bid), .s_axi_bresp(e_bresp), .s_axi_buser(e_buser),
        .s_axi_bvalid(e_bvalid), .s_axi_bready(e_bready),
        .busy_rd(), .busy_wr()
    );

    // ------------------------------------------------------------------------
    // Status snapshot back to aclk. The source side offers a fresh bundle
    // whenever the handshake is free, so the aclk copy trails ep_clk by one
    // round trip and is always internally consistent.
    // ------------------------------------------------------------------------
    localparam int SNAP_W = 2 * (NC * 32 + NC + 32);

    logic [SNAP_W-1:0] w_snap_src, w_snap_dst;
    logic              w_snap_dst_valid;

    assign w_snap_src = {w_rd_crc, w_rd_crc_v, w_rd_beats, w_wr_crc, w_wr_crc_v, w_wr_beats};

    cdc_2_phase_handshake #(
        .DATA_WIDTH(SNAP_W)
    ) u_status (
        .clk_src(ep_clk), .rst_src_n(ep_aresetn),
        .src_valid(1'b1), .src_ready(), .src_data(w_snap_src), .src_timeout(),
        .clk_dst(aclk), .rst_dst_n(aresetn),
        .dst_valid(w_snap_dst_valid), .dst_ready(1'b1), .dst_data(w_snap_dst)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_read_crc_value   <= '0;
            o_read_crc_valid   <= '0;
            o_read_beat_count  <= '0;
            o_write_crc_value  <= '0;
            o_write_crc_valid  <= '0;
            o_write_beat_count <= '0;
        end else if (w_snap_dst_valid) begin
            {o_read_crc_value, o_read_crc_valid, o_read_beat_count,
             o_write_crc_value, o_write_crc_valid, o_write_beat_count} <= w_snap_dst;
        end
    )

endmodule : fb_endpoints
