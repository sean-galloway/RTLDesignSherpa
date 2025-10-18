// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_converter
// Purpose: AXI4 Data Width Converter - Bidirectional (Upsize/Downsize)
//
// Description:
//   Converts between AXI4 interfaces of different data widths while maintaining
//   full protocol compliance. Supports both upsizing (narrow→wide) and downsizing
//   (wide→narrow) via parameterization.
//
//   Key Features:
//   - Bidirectional: Single module handles upsize OR downsize
//   - Full AXI4: All 5 channels (AW, W, B, AR, R) with complete signal support
//   - Burst preservation: Maintains burst semantics across conversion
//   - Error propagation: Correctly forwards SLVERR/DECERR responses
//   - GAXI FIFO buffering: Uses proven gaxi_fifo_sync for channel buffering
//
// Parameters:
//   S_AXI_DATA_WIDTH: Slave interface data width (8, 16, 32, 64, 128, 256, 512, 1024)
//   M_AXI_DATA_WIDTH: Master interface data width (8, 16, 32, 64, 128, 256, 512, 1024)
//   AXI_ID_WIDTH: Transaction ID width (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_USER_WIDTH: User signal width (0-1024)
//
// Status: Phase 1 - Skeleton and Infrastructure
//
// Documentation: rtl/amba/axi4/AXI4_DATA_WIDTH_CONVERTER_SPEC.md
// Subsystem: rtl/amba/axi4/
//
// Author: RTL Design Sherpa
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_dwidth_converter #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,           // Slave interface data width
    parameter int M_AXI_DATA_WIDTH  = 128,          // Master interface data width
    parameter int AXI_ID_WIDTH      = 8,            // Transaction ID width
    parameter int AXI_ADDR_WIDTH    = 32,           // Address bus width
    parameter int AXI_USER_WIDTH    = 1,            // User signal width

    // Buffer Depths (powers of 2)
    parameter int AW_FIFO_DEPTH     = 4,            // Write address FIFO depth (2^N)
    parameter int W_FIFO_DEPTH      = 8,            // Write data FIFO depth (2^N)
    parameter int B_FIFO_DEPTH      = 4,            // Write response FIFO depth (2^N)
    parameter int AR_FIFO_DEPTH     = 4,            // Read address FIFO depth (2^N)
    parameter int R_FIFO_DEPTH      = 8,            // Read data FIFO depth (2^N)

    // Calculated Parameters (do not override)
    parameter int S_STRB_WIDTH      = S_AXI_DATA_WIDTH / 8,
    parameter int M_STRB_WIDTH      = M_AXI_DATA_WIDTH / 8,
    parameter int WIDTH_RATIO       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                      (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                      (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    parameter bit UPSIZE            = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    parameter bit DOWNSIZE          = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    parameter int PTR_WIDTH         = $clog2(WIDTH_RATIO > 1 ? WIDTH_RATIO : 2)
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //--------------------------------------------------------------------------
    // Slave AXI Interface (Narrow in Upsize, Wide in Downsize)
    //--------------------------------------------------------------------------

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,      // Burst length - 1
    input  logic [2:0]                  s_axi_awsize,     // Bytes per beat
    input  logic [1:0]                  s_axi_awburst,    // FIXED/INCR/WRAP
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
    output logic [1:0]                  s_axi_bresp,     // OKAY/EXOKAY/SLVERR/DECERR
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [S_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //--------------------------------------------------------------------------
    // Master AXI Interface (Wide in Upsize, Narrow in Downsize)
    //--------------------------------------------------------------------------

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
    output logic                        m_axi_bready,

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_rid,
    input  logic [M_AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    //--------------------------------------------------------------------------
    // Status/Debug Interface
    //--------------------------------------------------------------------------
    output logic                        busy,
    output logic [15:0]                 wr_transactions_pending,
    output logic [15:0]                 rd_transactions_pending
);

    //==========================================================================
    // Parameter Validation
    //==========================================================================

    initial begin
        // Check data widths are powers of 2
        if (S_AXI_DATA_WIDTH != 2**$clog2(S_AXI_DATA_WIDTH)) begin
            $error("S_AXI_DATA_WIDTH must be power of 2");
        end
        if (M_AXI_DATA_WIDTH != 2**$clog2(M_AXI_DATA_WIDTH)) begin
            $error("M_AXI_DATA_WIDTH must be power of 2");
        end

        // Check width ratio is valid
        if (WIDTH_RATIO < 2) begin
            $error("WIDTH_RATIO must be >= 2 (no conversion needed if equal widths)");
        end
        if (WIDTH_RATIO > 16) begin
            $error("WIDTH_RATIO > 16 not supported (excessive buffering required)");
        end

        // Check only one mode is active
        if (UPSIZE && DOWNSIZE) begin
            $error("Both UPSIZE and DOWNSIZE cannot be 1 (configuration error)");
        end
        if (!UPSIZE && !DOWNSIZE) begin
            $error("Neither UPSIZE nor DOWNSIZE is 1 (widths must be different)");
        end

        // Display configuration
        $display("=== AXI4 Data Width Converter Configuration ===");
        $display("Mode: %s", UPSIZE ? "UPSIZE" : "DOWNSIZE");
        $display("Slave Width: %0d bits", S_AXI_DATA_WIDTH);
        $display("Master Width: %0d bits", M_AXI_DATA_WIDTH);
        $display("Width Ratio: %0d", WIDTH_RATIO);
        $display("ID Width: %0d", AXI_ID_WIDTH);
        $display("Addr Width: %0d", AXI_ADDR_WIDTH);
        $display("============================================");
    end

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // Write Address FIFO signals
    logic                        aw_fifo_valid;
    logic                        aw_fifo_ready;
    logic [AXI_ID_WIDTH-1:0]     aw_fifo_awid;
    logic [AXI_ADDR_WIDTH-1:0]   aw_fifo_awaddr;
    logic [7:0]                  aw_fifo_awlen;
    logic [2:0]                  aw_fifo_awsize;
    logic [1:0]                  aw_fifo_awburst;
    logic                        aw_fifo_awlock;
    logic [3:0]                  aw_fifo_awcache;
    logic [2:0]                  aw_fifo_awprot;
    logic [3:0]                  aw_fifo_awqos;
    logic [3:0]                  aw_fifo_awregion;
    logic [AXI_USER_WIDTH-1:0]   aw_fifo_awuser;

    // Read Address FIFO signals
    logic                        ar_fifo_valid;
    logic                        ar_fifo_ready;
    logic [AXI_ID_WIDTH-1:0]     ar_fifo_arid;
    logic [AXI_ADDR_WIDTH-1:0]   ar_fifo_araddr;
    logic [7:0]                  ar_fifo_arlen;
    logic [2:0]                  ar_fifo_arsize;
    logic [1:0]                  ar_fifo_arburst;
    logic                        ar_fifo_arlock;
    logic [3:0]                  ar_fifo_arcache;
    logic [2:0]                  ar_fifo_arprot;
    logic [3:0]                  ar_fifo_arqos;
    logic [3:0]                  ar_fifo_arregion;
    logic [AXI_USER_WIDTH-1:0]   ar_fifo_aruser;

    // Transaction tracking
    logic [15:0] wr_count;
    logic [15:0] rd_count;

    //==========================================================================
    // Phase 1: FIFO Infrastructure (Skeleton Implementation)
    //==========================================================================

    // Calculate FIFO data widths for address channels
    localparam int AW_FIFO_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 +
                                   4 + 3 + 4 + 4 + AXI_USER_WIDTH;
    localparam int AR_FIFO_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 +
                                   4 + 3 + 4 + 4 + AXI_USER_WIDTH;

    // Pack/unpack functions for address channels
    function automatic logic [AW_FIFO_WIDTH-1:0] pack_aw_channel;
        input logic [AXI_ID_WIDTH-1:0]   awid;
        input logic [AXI_ADDR_WIDTH-1:0] awaddr;
        input logic [7:0]                awlen;
        input logic [2:0]                awsize;
        input logic [1:0]                awburst;
        input logic                      awlock;
        input logic [3:0]                awcache;
        input logic [2:0]                awprot;
        input logic [3:0]                awqos;
        input logic [3:0]                awregion;
        input logic [AXI_USER_WIDTH-1:0] awuser;

        pack_aw_channel = {awid, awaddr, awlen, awsize, awburst, awlock,
                          awcache, awprot, awqos, awregion, awuser};
    endfunction

    //==========================================================================
    // Write Address FIFO
    //==========================================================================

    logic [AW_FIFO_WIDTH-1:0] aw_fifo_din;
    logic [AW_FIFO_WIDTH-1:0] aw_fifo_dout;
    logic aw_fifo_full;
    logic aw_fifo_empty;

    assign aw_fifo_din = pack_aw_channel(
        s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst,
        s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos,
        s_axi_awregion, s_axi_awuser
    );

    gaxi_fifo_sync #(
        .DATA_WIDTH(AW_FIFO_WIDTH),
        .DEPTH(AW_FIFO_DEPTH)
    ) u_aw_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_data     (aw_fifo_din),
        .wr_valid    (s_axi_awvalid),
        .wr_ready    (s_axi_awready),
        .rd_data     (aw_fifo_dout),
        .rd_valid    (aw_fifo_valid),
        .rd_ready    (aw_fifo_ready),
        .count       ()
    );

    // Unpack AW FIFO output (will be used in Phase 2)
    assign {aw_fifo_awid, aw_fifo_awaddr, aw_fifo_awlen, aw_fifo_awsize,
            aw_fifo_awburst, aw_fifo_awlock, aw_fifo_awcache, aw_fifo_awprot,
            aw_fifo_awqos, aw_fifo_awregion, aw_fifo_awuser} = aw_fifo_dout;

    //==========================================================================
    // Read Address FIFO
    //==========================================================================

    logic [AR_FIFO_WIDTH-1:0] ar_fifo_din;
    logic [AR_FIFO_WIDTH-1:0] ar_fifo_dout;
    logic ar_fifo_full;
    logic ar_fifo_empty;

    function automatic logic [AR_FIFO_WIDTH-1:0] pack_ar_channel;
        input logic [AXI_ID_WIDTH-1:0]   arid;
        input logic [AXI_ADDR_WIDTH-1:0] araddr;
        input logic [7:0]                arlen;
        input logic [2:0]                arsize;
        input logic [1:0]                arburst;
        input logic                      arlock;
        input logic [3:0]                arcache;
        input logic [2:0]                arprot;
        input logic [3:0]                arqos;
        input logic [3:0]                arregion;
        input logic [AXI_USER_WIDTH-1:0] aruser;

        pack_ar_channel = {arid, araddr, arlen, arsize, arburst, arlock,
                          arcache, arprot, arqos, arregion, aruser};
    endfunction

    assign ar_fifo_din = pack_ar_channel(
        s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst,
        s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos,
        s_axi_arregion, s_axi_aruser
    );

    gaxi_fifo_sync #(
        .DATA_WIDTH(AR_FIFO_WIDTH),
        .DEPTH(AR_FIFO_DEPTH)
    ) u_ar_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_data     (ar_fifo_din),
        .wr_valid    (s_axi_arvalid),
        .wr_ready    (s_axi_arready),
        .rd_data     (ar_fifo_dout),
        .rd_valid    (ar_fifo_valid),
        .rd_ready    (ar_fifo_ready),
        .count       ()
    );

    // Unpack AR FIFO output (will be used in Phase 2)
    assign {ar_fifo_arid, ar_fifo_araddr, ar_fifo_arlen, ar_fifo_arsize,
            ar_fifo_arburst, ar_fifo_arlock, ar_fifo_arcache, ar_fifo_arprot,
            ar_fifo_arqos, ar_fifo_arregion, ar_fifo_aruser} = ar_fifo_dout;

    //==========================================================================
    // Phase 2: UPSIZE Write Path Implementation
    //==========================================================================

    generate
        if (UPSIZE) begin : gen_upsize_write

            //------------------------------------------------------------------
            // Write Address (AW) Converter - Upsize Mode
            //------------------------------------------------------------------
            // Modify AWLEN: Divide by WIDTH_RATIO (e.g., 8 beats → 2 beats for 4:1)
            // Modify AWSIZE: Increase to master width (e.g., 2 → 4 for 32→128)
            // Address alignment enforced to master width boundary

            logic [7:0] master_awlen;
            logic [2:0] master_awsize;
            logic [AXI_ADDR_WIDTH-1:0] aligned_awaddr;
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);  // log2(bytes per beat)

            // Calculate master burst length (divide by ratio, round up)
            // Cast to 8-bit to match AWLEN width
            assign master_awlen = 8'((aw_fifo_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
            assign master_awsize = MASTER_SIZE[2:0];

            // Align address to master width boundary
            localparam int ALIGN_BITS = $clog2(M_STRB_WIDTH);
            assign aligned_awaddr = {aw_fifo_awaddr[AXI_ADDR_WIDTH-1:ALIGN_BITS], {ALIGN_BITS{1'b0}}};

            // Drive master AW channel
            assign aw_fifo_ready = m_axi_awready;
            assign m_axi_awid = aw_fifo_awid;
            assign m_axi_awaddr = aligned_awaddr;
            assign m_axi_awlen = master_awlen;
            assign m_axi_awsize = master_awsize;
            assign m_axi_awburst = aw_fifo_awburst;
            assign m_axi_awlock = aw_fifo_awlock;
            assign m_axi_awcache = aw_fifo_awcache;
            assign m_axi_awprot = aw_fifo_awprot;
            assign m_axi_awqos = aw_fifo_awqos;
            assign m_axi_awregion = aw_fifo_awregion;
            assign m_axi_awuser = aw_fifo_awuser;
            assign m_axi_awvalid = aw_fifo_valid;

            //------------------------------------------------------------------
            // Write Data (W) Accumulator - Upsize Mode
            //------------------------------------------------------------------
            // Accumulate WIDTH_RATIO narrow beats into 1 wide beat
            // Merge WSTRB across accumulated beats
            // Issue wide beat when accumulator full or WLAST received

            logic [M_AXI_DATA_WIDTH-1:0] r_wdata_accumulator;
            logic [M_STRB_WIDTH-1:0]     r_wstrb_accumulator;
            logic [PTR_WIDTH-1:0]        r_beat_pointer;
            logic                        r_wlast_seen;

            always_ff @(posedge aclk or negedge aresetn) begin
                if (!aresetn) begin
                    r_wdata_accumulator <= '0;
                    r_wstrb_accumulator <= '0;
                    r_beat_pointer <= '0;
                    r_wlast_seen <= 1'b0;
                end else if (s_axi_wvalid && s_axi_wready) begin
                    // Accumulate narrow beat into wide accumulator
                    r_wdata_accumulator[r_beat_pointer*S_AXI_DATA_WIDTH +: S_AXI_DATA_WIDTH] <= s_axi_wdata;
                    r_wstrb_accumulator[r_beat_pointer*S_STRB_WIDTH +: S_STRB_WIDTH] <= s_axi_wstrb;

                    // Track WLAST
                    if (s_axi_wlast) begin
                        r_wlast_seen <= 1'b1;
                    end

                    // Increment pointer or reset when issuing wide beat
                    if (r_beat_pointer == PTR_WIDTH'(WIDTH_RATIO-1) || s_axi_wlast) begin
                        r_beat_pointer <= '0;
                        r_wlast_seen <= 1'b0;
                    end else begin
                        r_beat_pointer <= r_beat_pointer + 1'b1;
                    end
                end else if (m_axi_wvalid && m_axi_wready) begin
                    // Clear after master accepts
                    r_wdata_accumulator <= '0;
                    r_wstrb_accumulator <= '0;
                end
            end

            // Issue wide beat when accumulator full or partial beat at end of burst
            logic w_issue_wide_beat;
            assign w_issue_wide_beat = (r_beat_pointer == PTR_WIDTH'(WIDTH_RATIO-1)) || r_wlast_seen;

            // Drive master W channel
            assign s_axi_wready = !w_issue_wide_beat || m_axi_wready;
            assign m_axi_wdata = r_wdata_accumulator;
            assign m_axi_wstrb = r_wstrb_accumulator;
            assign m_axi_wlast = r_wlast_seen;
            assign m_axi_wuser = s_axi_wuser;  // Forward user signal
            assign m_axi_wvalid = w_issue_wide_beat;

            //------------------------------------------------------------------
            // Write Response (B) Pass-Through - Upsize Mode
            //------------------------------------------------------------------
            // No conversion needed - single response for entire burst

            assign s_axi_bid = m_axi_bid;
            assign s_axi_bresp = m_axi_bresp;
            assign s_axi_buser = m_axi_buser;
            assign s_axi_bvalid = m_axi_bvalid;
            assign m_axi_bready = s_axi_bready;

        end else begin : gen_downsize_write

            //------------------------------------------------------------------
            // Downsize Write Path (Phase 4 - TODO)
            //------------------------------------------------------------------

            // Temporary pass-through for downsize
            assign aw_fifo_ready = m_axi_awready;
            assign m_axi_awid = aw_fifo_awid;
            assign m_axi_awaddr = aw_fifo_awaddr;
            assign m_axi_awlen = aw_fifo_awlen;
            assign m_axi_awsize = aw_fifo_awsize;
            assign m_axi_awburst = aw_fifo_awburst;
            assign m_axi_awlock = aw_fifo_awlock;
            assign m_axi_awcache = aw_fifo_awcache;
            assign m_axi_awprot = aw_fifo_awprot;
            assign m_axi_awqos = aw_fifo_awqos;
            assign m_axi_awregion = aw_fifo_awregion;
            assign m_axi_awuser = aw_fifo_awuser;
            assign m_axi_awvalid = aw_fifo_valid;

            assign s_axi_wready = m_axi_wready;
            assign m_axi_wdata = s_axi_wdata[M_AXI_DATA_WIDTH-1:0];
            assign m_axi_wstrb = s_axi_wstrb[M_STRB_WIDTH-1:0];
            assign m_axi_wlast = s_axi_wlast;
            assign m_axi_wuser = s_axi_wuser;
            assign m_axi_wvalid = s_axi_wvalid;

            assign s_axi_bid = m_axi_bid;
            assign s_axi_bresp = m_axi_bresp;
            assign s_axi_buser = m_axi_buser;
            assign s_axi_bvalid = m_axi_bvalid;
            assign m_axi_bready = s_axi_bready;

        end
    endgenerate

    //==========================================================================
    // Read Path (AR, R channels) - Phase 3/5 TODO
    //==========================================================================

    // AR channel pass-through (temporary)
    assign ar_fifo_ready = m_axi_arready;
    assign m_axi_arid = ar_fifo_arid;
    assign m_axi_araddr = ar_fifo_araddr;
    assign m_axi_arlen = ar_fifo_arlen;
    assign m_axi_arsize = ar_fifo_arsize;
    assign m_axi_arburst = ar_fifo_arburst;
    assign m_axi_arlock = ar_fifo_arlock;
    assign m_axi_arcache = ar_fifo_arcache;
    assign m_axi_arprot = ar_fifo_arprot;
    assign m_axi_arqos = ar_fifo_arqos;
    assign m_axi_arregion = ar_fifo_arregion;
    assign m_axi_aruser = ar_fifo_aruser;
    assign m_axi_arvalid = ar_fifo_valid;

    // R channel pass-through (temporary)
    assign s_axi_rid = m_axi_rid;
    assign s_axi_rdata = m_axi_rdata[S_AXI_DATA_WIDTH-1:0];
    assign s_axi_rresp = m_axi_rresp;
    assign s_axi_rlast = m_axi_rlast;
    assign s_axi_ruser = m_axi_ruser;
    assign s_axi_rvalid = m_axi_rvalid;
    assign m_axi_rready = s_axi_rready;

    //==========================================================================
    // Transaction Tracking (Simple Counters for Phase 1)
    //==========================================================================

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            wr_count <= 16'h0;
            rd_count <= 16'h0;
        end else begin
            // Increment on AW handshake, decrement on B handshake
            if (s_axi_awvalid && s_axi_awready && !(s_axi_bvalid && s_axi_bready)) begin
                wr_count <= wr_count + 1'b1;
            end else if (!(s_axi_awvalid && s_axi_awready) && (s_axi_bvalid && s_axi_bready)) begin
                wr_count <= wr_count - 1'b1;
            end

            // Increment on AR handshake, decrement on R LAST handshake
            if (s_axi_arvalid && s_axi_arready && !(s_axi_rvalid && s_axi_rready && s_axi_rlast)) begin
                rd_count <= rd_count + 1'b1;
            end else if (!(s_axi_arvalid && s_axi_arready) && (s_axi_rvalid && s_axi_rready && s_axi_rlast)) begin
                rd_count <= rd_count - 1'b1;
            end
        end
    end

    assign wr_transactions_pending = wr_count;
    assign rd_transactions_pending = rd_count;
    assign busy = (wr_count != 0) || (rd_count != 0);

endmodule : axi4_dwidth_converter
