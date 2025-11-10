// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_converter_rd
// Purpose: AXI4 Read Data Width Converter (READ-ONLY, STANDALONE)
//
// Description:
//   Converts between AXI4 read interfaces of different data widths.
//   Handles ONLY read path (AR, R channels) - no write support.
//
//   Standalone implementation with gaxi_skid_buffer for timing closure.
//   For write conversion, use axi4_dwidth_converter_wr.sv.
//
//   Key Features:
//   - Read-only: AR, R channels only
//   - Bidirectional: Single module handles upsize OR downsize
//   - Timing closure: Uses gaxi_skid_buffer on all channels
//   - Full AXI4: All read channel signals
//   - Burst preservation: Maintains burst semantics
//
// Parameters:
//   S_AXI_DATA_WIDTH: Slave interface data width (32, 64, 128, 256)
//   M_AXI_DATA_WIDTH: Master interface data width (32, 64, 128, 256)
//   AXI_ID_WIDTH: Transaction ID width (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_USER_WIDTH: User signal width (0-1024)
//   SKID_DEPTH_AR: AR channel skid buffer depth (2-8, default 2)
//   SKID_DEPTH_R: R channel skid buffer depth (2-8, default 4)
//
// Author: RTL Design Sherpa
// Created: 2025-10-24

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_dwidth_converter_rd #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam int PTR_WIDTH    = $clog2(WIDTH_RATIO),

    // Skid buffer packed widths
    localparam int AR_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int R_WIDTH  = S_AXI_DATA_WIDTH + 2 + AXI_USER_WIDTH + 1 + AXI_ID_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Read Interface
    //==========================================================================

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

    //==========================================================================
    // Master AXI Read Interface
    //==========================================================================

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
    output logic                        m_axi_rready
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

        $display("======================================");
        $display("AXI4 Read Data Width Converter");
        $display("Mode: %s", UPSIZE ? "UPSIZE" : "DOWNSIZE");
        $display("Slave Width: %0d bits", S_AXI_DATA_WIDTH);
        $display("Master Width: %0d bits", M_AXI_DATA_WIDTH);
        $display("Width Ratio: %0d", WIDTH_RATIO);
        $display("======================================");
    end

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // AR channel skid buffer signals
    logic [AR_WIDTH-1:0]         int_ar_data;
    logic                        int_ar_valid;
    logic                        int_ar_ready;

    logic [AXI_ID_WIDTH-1:0]     int_arid;
    logic [AXI_ADDR_WIDTH-1:0]   int_araddr;
    logic [7:0]                  int_arlen;
    logic [2:0]                  int_arsize;
    logic [1:0]                  int_arburst;
    logic                        int_arlock;
    logic [3:0]                  int_arcache;
    logic [2:0]                  int_arprot;
    logic [3:0]                  int_arqos;
    logic [3:0]                  int_arregion;
    logic [AXI_USER_WIDTH-1:0]   int_aruser;

    // R channel skid buffer signals
    logic [R_WIDTH-1:0]          int_r_data;
    logic                        int_r_valid;
    logic                        int_r_ready;

    logic [AXI_ID_WIDTH-1:0]     int_rid;
    logic [S_AXI_DATA_WIDTH-1:0] int_rdata;
    logic [1:0]                  int_rresp;
    logic                        int_rlast;
    logic [AXI_USER_WIDTH-1:0]   int_ruser;

    //==========================================================================
    // AR Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(AR_WIDTH),
        .INSTANCE_NAME("AR_SKID")
    ) ar_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axi_arvalid),
        .wr_ready   (s_axi_arready),
        .wr_data    ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize,
                      s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot,
                      s_axi_arqos, s_axi_arregion, s_axi_aruser}),
        .rd_valid   (int_ar_valid),
        .rd_ready   (int_ar_ready),
        .rd_data    (int_ar_data),
        .count      (),
        .rd_count   ()
    );

    // Unpack AR skid buffer output
    assign {int_arid, int_araddr, int_arlen, int_arsize, int_arburst,
            int_arlock, int_arcache, int_arprot, int_arqos, int_arregion,
            int_aruser} = int_ar_data;

    //==========================================================================
    // R Channel Skid Buffer (Timing Closure - Reverse Direction)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(R_WIDTH),
        .INSTANCE_NAME("R_SKID")
    ) r_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (int_r_valid),
        .wr_ready   (int_r_ready),
        .wr_data    (int_r_data),
        .rd_valid   (s_axi_rvalid),
        .rd_ready   (s_axi_rready),
        .rd_data    ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
        .count      (),
        .rd_count   ()
    );

    // Pack R channel for skid buffer input
    assign int_r_data = {int_rid, int_rdata, int_rresp, int_rlast, int_ruser};

    //==========================================================================
    // Read Address Channel Conversion
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_ar_downsize
            // Downsize: Wide→Narrow
            // Multiply burst length by ratio
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign m_axi_arid     = int_arid;
            assign m_axi_araddr   = int_araddr;
            assign m_axi_arlen    = ((int_arlen + 8'd1) * 8'(WIDTH_RATIO)) - 8'd1;
            assign m_axi_arsize   = MASTER_SIZE[2:0];
            assign m_axi_arburst  = int_arburst;
            assign m_axi_arlock   = int_arlock;
            assign m_axi_arcache  = int_arcache;
            assign m_axi_arprot   = int_arprot;
            assign m_axi_arqos    = int_arqos;
            assign m_axi_arregion = int_arregion;
            assign m_axi_aruser   = int_aruser;
            assign m_axi_arvalid  = int_ar_valid;
            assign int_ar_ready   = m_axi_arready;

        end else begin : gen_ar_upsize
            // Upsize: Narrow→Wide
            // Divide burst length by ratio, align address
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int ALIGN_BITS  = $clog2(M_STRB_WIDTH);

            logic [7:0] master_arlen;
            logic [AXI_ADDR_WIDTH-1:0] aligned_araddr;

            assign master_arlen = 8'((int_arlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
            assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH-1:ALIGN_BITS], {ALIGN_BITS{1'b0}}};

            assign m_axi_arid     = int_arid;
            assign m_axi_araddr   = aligned_araddr;
            assign m_axi_arlen    = master_arlen;
            assign m_axi_arsize   = MASTER_SIZE[2:0];
            assign m_axi_arburst  = int_arburst;
            assign m_axi_arlock   = int_arlock;
            assign m_axi_arcache  = int_arcache;
            assign m_axi_arprot   = int_arprot;
            assign m_axi_arqos    = int_arqos;
            assign m_axi_arregion = int_arregion;
            assign m_axi_aruser   = int_aruser;
            assign m_axi_arvalid  = int_ar_valid;
            assign int_ar_ready   = m_axi_arready;

        end
    endgenerate

    //==========================================================================
    // Read Data Channel Conversion
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_r_downsize
            // Downsize: Wide→Narrow
            // Accumulate WIDTH_RATIO narrow beats into 1 wide beat

            logic [S_AXI_DATA_WIDTH-1:0] r_rdata_accumulator;
            logic [PTR_WIDTH-1:0]        r_accum_ptr;
            logic                        r_wide_beat_valid;
            logic                        r_rlast_buffered;
            logic [1:0]                  r_rresp_buffered;
            logic [AXI_ID_WIDTH-1:0]     r_rid_buffered;
            logic [AXI_USER_WIDTH-1:0]   r_ruser_buffered;

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    r_rdata_accumulator <= '0;
                    r_accum_ptr <= '0;
                    r_wide_beat_valid <= 1'b0;
                    r_rlast_buffered <= 1'b0;
                    r_rresp_buffered <= 2'b00;
                    r_rid_buffered <= '0;
                    r_ruser_buffered <= '0;
                end else begin
                    // Accept narrow beat from master
                    if (m_axi_rvalid && m_axi_rready) begin
                        // Accumulate narrow beat
                        r_rdata_accumulator[r_accum_ptr*M_AXI_DATA_WIDTH +: M_AXI_DATA_WIDTH] <= m_axi_rdata;

                        // Track ID, response, user (first beat sets these)
                        if (r_accum_ptr == '0) begin
                            r_rid_buffered <= m_axi_rid;
                            r_rresp_buffered <= m_axi_rresp;
                            r_ruser_buffered <= m_axi_ruser;
                        end else begin
                            // OR together RRESP (any error propagates)
                            r_rresp_buffered <= r_rresp_buffered | m_axi_rresp;
                        end

                        // Check if complete wide beat ready
                        if (r_accum_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || m_axi_rlast) begin
                            r_wide_beat_valid <= 1'b1;
                            r_accum_ptr <= '0;
                            r_rlast_buffered <= m_axi_rlast;
                        end else begin
                            r_accum_ptr <= r_accum_ptr + 1'b1;
                        end
                    end

                    // Slave accepts wide beat
                    if (r_wide_beat_valid && int_r_ready) begin
                        r_wide_beat_valid <= 1'b0;
                        r_rlast_buffered <= 1'b0;
                    end
                end
            )

            // Drive internal R channel
            assign int_rdata  = r_rdata_accumulator;
            assign int_rid    = r_rid_buffered;
            assign int_rresp  = r_rresp_buffered;
            assign int_rlast  = r_rlast_buffered && r_wide_beat_valid;
            assign int_ruser  = r_ruser_buffered;
            assign int_r_valid = r_wide_beat_valid;

            // Master ready when we're accumulating or slave ready
            assign m_axi_rready = !r_wide_beat_valid || int_r_ready;

        end else begin : gen_r_upsize
            // Upsize: Narrow→Wide
            // Split each wide beat into WIDTH_RATIO narrow beats

            logic [M_AXI_DATA_WIDTH-1:0] r_rdata_buffer;
            logic [1:0]                  r_rresp_buffer;
            logic [AXI_USER_WIDTH-1:0]   r_ruser_buffer;
            logic [AXI_ID_WIDTH-1:0]     r_rid_buffer;
            logic [PTR_WIDTH-1:0]        r_beat_ptr;
            logic                        r_wide_buffered;
            logic                        r_rlast_buffered;

            // Burst tracking
            logic [7:0]                  r_slave_beat_count;
            logic [7:0]                  r_slave_total_beats;
            logic                        r_burst_active;

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    r_rdata_buffer <= '0;
                    r_rresp_buffer <= '0;
                    r_ruser_buffer <= '0;
                    r_rid_buffer <= '0;
                    r_beat_ptr <= '0;
                    r_wide_buffered <= 1'b0;
                    r_rlast_buffered <= 1'b0;
                    r_slave_beat_count <= '0;
                    r_slave_total_beats <= '0;
                    r_burst_active <= 1'b0;
                end else begin
                    // Start new burst
                    if (int_ar_valid && int_ar_ready && !r_burst_active) begin
                        r_slave_total_beats <= int_arlen + 8'd1;
                        r_slave_beat_count <= '0;
                        r_burst_active <= 1'b1;
                    end

                    // Accept wide beat from master
                    if (m_axi_rvalid && m_axi_rready && !r_wide_buffered) begin
                        r_rdata_buffer <= m_axi_rdata;
                        r_rresp_buffer <= m_axi_rresp;
                        r_ruser_buffer <= m_axi_ruser;
                        r_rid_buffer <= m_axi_rid;
                        r_rlast_buffered <= m_axi_rlast;
                        r_wide_buffered <= 1'b1;
                        r_beat_ptr <= '0;
                    end

                    // Send narrow beat to slave
                    if (r_wide_buffered && int_r_ready && r_burst_active) begin
                        if (r_slave_beat_count + 8'd1 >= r_slave_total_beats) begin
                            // Last slave beat - end burst
                            r_wide_buffered <= 1'b0;
                            r_beat_ptr <= '0;
                            r_slave_beat_count <= '0;
                            r_burst_active <= 1'b0;
                        end else if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) begin
                            // Last narrow beat from wide beat, more beats needed
                            r_wide_buffered <= 1'b0;
                            r_beat_ptr <= '0;
                            r_slave_beat_count <= r_slave_beat_count + 8'd1;
                        end else begin
                            // More narrow beats from this wide beat
                            r_beat_ptr <= r_beat_ptr + 1'b1;
                            r_slave_beat_count <= r_slave_beat_count + 8'd1;
                        end
                    end
                end
)

            // Determine last slave beat
            logic w_last_slave_beat;
            assign w_last_slave_beat = (r_slave_beat_count + 8'd1 >= r_slave_total_beats);

            // Master ready when buffer empty or sending last beat
            assign m_axi_rready = !r_wide_buffered || (int_r_ready && w_last_slave_beat);

            // Drive internal R channel
            assign int_r_valid = r_wide_buffered && r_burst_active;
            assign int_rdata   = r_rdata_buffer[r_beat_ptr*S_AXI_DATA_WIDTH +: S_AXI_DATA_WIDTH];
            assign int_rresp   = r_rresp_buffer;
            assign int_ruser   = r_ruser_buffer;
            assign int_rid     = r_rid_buffer;
            assign int_rlast   = r_wide_buffered && w_last_slave_beat;

        end
    endgenerate

endmodule : axi4_dwidth_converter_rd
