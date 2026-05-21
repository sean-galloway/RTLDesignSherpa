// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_converter_wr
// Purpose: AXI4 Write Data Width Converter (WRITE-ONLY, STANDALONE)
//
// Description:
//   Converts between AXI4 write interfaces of different data widths.
//   Handles ONLY write path (AW, W, B channels) - no read support.
//
//   The W channel data path is delegated to the validated
//   axi_data_upsize / axi_data_dnsize primitives in this same
//   directory (each with its own pytest suite). This wrapper still
//   owns: AW/W/B skid buffers, the AW awlen/awsize rewrite, the
//   wuser carry that the primitives don't handle, and the B channel
//   pass-through.
//
//   For read conversion, use axi4_dwidth_converter_rd.sv.
//
// Parameters:
//   S_AXI_DATA_WIDTH: Slave interface data width (32, 64, 128, 256)
//   M_AXI_DATA_WIDTH: Master interface data width (32, 64, 128, 256)
//   AXI_ID_WIDTH: Transaction ID width (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_USER_WIDTH: User signal width (0-1024)
//   SKID_DEPTH_AW: AW channel skid buffer depth (2-8, default 2)
//   SKID_DEPTH_W: W channel skid buffer depth (2-8, default 4)
//   SKID_DEPTH_B: B channel skid buffer depth (2-8, default 2)
//
// Author: RTL Design Sherpa
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_dwidth_converter_wr #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    // Skid buffer packed widths
    localparam int AW_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int W_WIDTH  = S_AXI_DATA_WIDTH + S_STRB_WIDTH + 1 + AXI_USER_WIDTH,
    localparam int B_WIDTH  = AXI_ID_WIDTH + 2 + AXI_USER_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Write Interface
    //==========================================================================

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write Data Channel
    input  logic [S_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [S_STRB_WIDTH-1:0]     s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI Write Interface
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // Write Data Channel
    output logic [M_AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [M_STRB_WIDTH-1:0]     m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);

    //==========================================================================
    // Parameter Validation
    //==========================================================================

    initial begin
        if (S_AXI_DATA_WIDTH != 2**$clog2(S_AXI_DATA_WIDTH))
            $error("S_AXI_DATA_WIDTH must be power of 2");
        if (M_AXI_DATA_WIDTH != 2**$clog2(M_AXI_DATA_WIDTH))
            $error("M_AXI_DATA_WIDTH must be power of 2");
        if (WIDTH_RATIO < 2)
            $error("WIDTH_RATIO must be >= 2");
        if (!UPSIZE && !DOWNSIZE)
            $error("Must be either UPSIZE or DOWNSIZE mode");
    end

    //==========================================================================
    // Internal Signals - AW Channel (after skid buffer, before conversion)
    //==========================================================================

    logic [AW_WIDTH-1:0]       int_aw_data;
    logic                      int_aw_valid;
    logic                      int_aw_ready;

    logic [AXI_ID_WIDTH-1:0]   int_awid;
    logic [AXI_ADDR_WIDTH-1:0] int_awaddr;
    logic [7:0]                int_awlen;
    logic [2:0]                int_awsize;
    logic [1:0]                int_awburst;
    logic                      int_awlock;
    logic [3:0]                int_awcache;
    logic [2:0]                int_awprot;
    logic [3:0]                int_awqos;
    logic [3:0]                int_awregion;
    logic [AXI_USER_WIDTH-1:0] int_awuser;

    //==========================================================================
    // Internal Signals - W Channel (after skid buffer, before conversion)
    //==========================================================================

    logic [W_WIDTH-1:0]          int_w_data;
    logic                        int_w_valid;
    logic                        int_w_ready;

    logic [S_AXI_DATA_WIDTH-1:0] int_wdata;
    logic [S_STRB_WIDTH-1:0]     int_wstrb;
    logic                        int_wlast;
    logic [AXI_USER_WIDTH-1:0]   int_wuser;

    //==========================================================================
    // Internal Signals - B Channel (before skid buffer, after pass-through)
    //==========================================================================

    logic [B_WIDTH-1:0]        int_b_data;
    logic                      int_b_valid;
    logic                      int_b_ready;

    logic [AXI_ID_WIDTH-1:0]   int_bid;
    logic [1:0]                int_bresp;
    logic [AXI_USER_WIDTH-1:0] int_buser;

    //==========================================================================
    // AW Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AW_WIDTH)
    ) aw_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axi_awvalid),
        .wr_ready   (s_axi_awready),
        .wr_data    ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize,
                      s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot,
                      s_axi_awqos, s_axi_awregion, s_axi_awuser}),
        .rd_valid   (int_aw_valid),
        .rd_ready   (int_aw_ready),
        .rd_data    (int_aw_data),
        .count      (),
        .rd_count   ()
    );

    assign {int_awid, int_awaddr, int_awlen, int_awsize, int_awburst,
            int_awlock, int_awcache, int_awprot, int_awqos, int_awregion,
            int_awuser} = int_aw_data;

    //==========================================================================
    // W Channel Skid Buffer (Timing + Data Buffering)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(W_WIDTH)
    ) w_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axi_wvalid),
        .wr_ready   (s_axi_wready),
        .wr_data    ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
        .rd_valid   (int_w_valid),
        .rd_ready   (int_w_ready),
        .rd_data    (int_w_data),
        .count      (),
        .rd_count   ()
    );

    assign {int_wdata, int_wstrb, int_wlast, int_wuser} = int_w_data;

    //==========================================================================
    // B Channel Skid Buffer (Timing Closure - Reverse Direction)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(B_WIDTH)
    ) b_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (int_b_valid),
        .wr_ready   (int_b_ready),
        .wr_data    (int_b_data),
        .rd_valid   (s_axi_bvalid),
        .rd_ready   (s_axi_bready),
        .rd_data    ({s_axi_bid, s_axi_bresp, s_axi_buser}),
        .count      (),
        .rd_count   ()
    );

    assign int_b_data = {int_bid, int_bresp, int_buser};

    //==========================================================================
    // Write Address Channel Conversion (awlen/awsize rewrite)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_aw_downsize
            // Downsize: slave (wide) → master (narrow). Multiply slave's
            // burst length by ratio so master moves the same total bytes
            // in narrow beats.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            assign m_axi_awlen    = ((int_awlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1;
            assign m_axi_awsize   = MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            assign m_axi_awvalid  = int_aw_valid;
            assign int_aw_ready   = m_axi_awready;

        end else begin : gen_aw_upsize
            // Upsize: slave (narrow) → master (wide). Divide burst length
            // by ratio (round up).
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            assign m_axi_awlen    = ((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
            assign m_axi_awsize   = MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            assign m_axi_awvalid  = int_aw_valid;
            assign int_aw_ready   = m_axi_awready;
        end
    endgenerate

    //==========================================================================
    // W Channel WUSER Carry
    //
    //   The validated axi_data_{upsize,dnsize} primitives carry only one
    //   sideband (WSTRB on the W channel). WUSER stays constant within a
    //   burst in normal AXI4 traffic, so we register the latest value
    //   from the slave-side W handshake and present it on every
    //   master-side W beat.
    //==========================================================================

    logic [AXI_USER_WIDTH-1:0] r_wuser_held;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wuser_held <= '0;
        end else if (int_w_valid && int_w_ready) begin
            r_wuser_held <= int_wuser;
        end
    )

    assign m_axi_wuser = r_wuser_held;

    //==========================================================================
    // W Channel Data Conversion (delegates to validated primitives)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_w_downsize
            // Slave wide, master narrow. W direction: slave → master, so
            // wide → narrow. axi_data_dnsize with TRACK_BURSTS=0 — the
            // slave's wlast drives narrow_last on the final narrow beat
            // from the last wide beat (matches the master's awlen rewrite).
            // WSTRB slices per narrow beat: SB_BROADCAST=0.
            axi_data_dnsize #(
                .WIDE_WIDTH      (S_AXI_DATA_WIDTH),
                .NARROW_WIDTH    (M_AXI_DATA_WIDTH),
                .WIDE_SB_WIDTH   (S_STRB_WIDTH),
                .NARROW_SB_WIDTH (M_STRB_WIDTH),
                .SB_BROADCAST    (0),
                .TRACK_BURSTS    (0),
                .BURST_LEN_WIDTH (8),
                .DUAL_BUFFER     (0)
            ) u_w_dnsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .burst_len       (8'd0),
                .burst_start     (1'b0),
                .wide_valid      (int_w_valid),
                .wide_ready      (int_w_ready),
                .wide_data       (int_wdata),
                .wide_sideband   (int_wstrb),
                .wide_last       (int_wlast),
                .narrow_valid    (m_axi_wvalid),
                .narrow_ready    (m_axi_wready),
                .narrow_data     (m_axi_wdata),
                .narrow_sideband (m_axi_wstrb),
                .narrow_last     (m_axi_wlast)
            );

        end else begin : gen_w_upsize
            // Slave narrow, master wide. W direction: slave → master, so
            // narrow → wide. axi_data_upsize concatenates WSTRBs:
            // SB_OR_MODE=0. wlast on the narrow side terminates the
            // accumulation early (matches existing UPSIZE semantics).
            axi_data_upsize #(
                .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (S_STRB_WIDTH),
                .WIDE_SB_WIDTH   (M_STRB_WIDTH),
                .SB_OR_MODE      (0)
            ) u_w_upsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .narrow_valid    (int_w_valid),
                .narrow_ready    (int_w_ready),
                .narrow_data     (int_wdata),
                .narrow_sideband (int_wstrb),
                .narrow_last     (int_wlast),
                .wide_valid      (m_axi_wvalid),
                .wide_ready      (m_axi_wready),
                .wide_data       (m_axi_wdata),
                .wide_sideband   (m_axi_wstrb),
                .wide_last       (m_axi_wlast)
            );
        end
    endgenerate

    //==========================================================================
    // Write Response Channel (Pass-Through)
    //==========================================================================

    assign int_bid     = m_axi_bid;
    assign int_bresp   = m_axi_bresp;
    assign int_buser   = m_axi_buser;
    assign int_b_valid = m_axi_bvalid;
    assign m_axi_bready = int_b_ready;

endmodule : axi4_dwidth_converter_wr
