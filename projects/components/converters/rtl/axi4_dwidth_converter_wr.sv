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
//   Standalone implementation with gaxi_skid_buffer for timing closure.
//   For read conversion, use axi4_dwidth_converter_rd.sv.
//
//   Key Features:
//   - Write-only: AW, W, B channels only
//   - Bidirectional: Single module handles upsize OR downsize
//   - Timing closure: Uses gaxi_skid_buffer on all channels
//   - Full AXI4: All write channel signals
//   - Burst preservation: Maintains burst semantics
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
    localparam int PTR_WIDTH    = $clog2(WIDTH_RATIO),

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

        $display("=== AXI4 Write Data Width Converter ===");
        $display("Mode: %s", UPSIZE ? "UPSIZE" : "DOWNSIZE");
        $display("Slave Width: %0d bits", S_AXI_DATA_WIDTH);
        $display("Master Width: %0d bits", M_AXI_DATA_WIDTH);
        $display("Width Ratio: %0d", WIDTH_RATIO);
        $display("Skid Depths: AW=%0d W=%0d B=%0d", SKID_DEPTH_AW, SKID_DEPTH_W, SKID_DEPTH_B);
        $display("=======================================");
    end

    //==========================================================================
    // Internal Signals - AW Channel (after skid buffer, before conversion)
    //==========================================================================

    logic [AW_WIDTH-1:0] int_aw_data;
    logic                int_aw_valid;
    logic                int_aw_ready;

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

    logic [W_WIDTH-1:0] int_w_data;
    logic               int_w_valid;
    logic               int_w_ready;

    logic [S_AXI_DATA_WIDTH-1:0] int_wdata;
    logic [S_STRB_WIDTH-1:0]     int_wstrb;
    logic                        int_wlast;
    logic [AXI_USER_WIDTH-1:0]   int_wuser;

    //==========================================================================
    // Internal Signals - B Channel (before skid buffer, after pass-through)
    //==========================================================================

    logic [B_WIDTH-1:0]      int_b_data;
    logic                    int_b_valid;
    logic                    int_b_ready;

    logic [AXI_ID_WIDTH-1:0]   int_bid;
    logic [1:0]                int_bresp;
    logic [AXI_USER_WIDTH-1:0] int_buser;

    //==========================================================================
    // AW Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AW_WIDTH),
        .INSTANCE_NAME("AW_SKID")
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

    // Unpack AW skid buffer output
    assign {int_awid, int_awaddr, int_awlen, int_awsize, int_awburst,
            int_awlock, int_awcache, int_awprot, int_awqos, int_awregion,
            int_awuser} = int_aw_data;

    //==========================================================================
    // W Channel Skid Buffer (Timing + Data Buffering)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(W_WIDTH),
        .INSTANCE_NAME("W_SKID")
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

    // Unpack W skid buffer output
    assign {int_wdata, int_wstrb, int_wlast, int_wuser} = int_w_data;

    //==========================================================================
    // B Channel Skid Buffer (Timing Closure - Reverse Direction)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(B_WIDTH),
        .INSTANCE_NAME("B_SKID")
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

    // Pack B channel for skid buffer input
    assign int_b_data = {int_bid, int_bresp, int_buser};

    //==========================================================================
    // Write Address Channel Conversion
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_aw_downsize
            // Downsize: Wide→Narrow
            // Multiply burst length by ratio
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
            // Upsize: Narrow→Wide
            // Divide burst length by ratio (rounding up for partial bursts)
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            // Round up: (num_slave_beats + ratio - 1) / ratio
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
    // Write Data Channel Conversion
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_w_downsize
            // Downsize: Split wide beats into narrow beats
            // No FSM - just a counter. Counter value IS the state.

            // Wide beat buffer
            logic [S_AXI_DATA_WIDTH-1:0] r_wdata_buffer;
            logic [S_STRB_WIDTH-1:0]     r_wstrb_buffer;
            logic [AXI_USER_WIDTH-1:0]   r_wuser_buffer;
            logic                        r_wlast_buffered;
            logic [PTR_WIDTH:0]          r_beat_index;  // 0-3: valid, 4: empty (need extra bit)

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    r_wdata_buffer <= '0;
                    r_wstrb_buffer <= '0;
                    r_wuser_buffer <= '0;
                    r_wlast_buffered <= 1'b0;
                    r_beat_index <= (PTR_WIDTH+1)'(WIDTH_RATIO);  // Empty
                end else begin
                    logic accepting_wide_beat;
                    logic sending_narrow_beat;

                    accepting_wide_beat = int_w_valid && int_w_ready;
                    sending_narrow_beat = m_axi_wvalid && m_axi_wready;

                    // Load new wide beat (resets counter to 0)
                    if (accepting_wide_beat) begin
                        r_wdata_buffer <= int_wdata;
                        r_wstrb_buffer <= int_wstrb;
                        r_wuser_buffer <= int_wuser;
                        r_wlast_buffered <= int_wlast;
                        r_beat_index <= '0;
                    end
                    // Send narrow beat (increment counter, mark empty when done)
                    else if (sending_narrow_beat) begin
                        r_beat_index <= r_beat_index + 1'b1;
                    end
                    // else: hold
                end
)


            // Output logic - counter encodes all state
            wire buffer_valid = (r_beat_index < (PTR_WIDTH+1)'(WIDTH_RATIO));
            wire last_beat    = (r_beat_index == (PTR_WIDTH+1)'(WIDTH_RATIO-1));

            assign int_w_ready  = !buffer_valid || (m_axi_wready && last_beat);
            assign m_axi_wvalid = buffer_valid;
            assign m_axi_wdata  = r_wdata_buffer[r_beat_index[PTR_WIDTH-1:0]*M_AXI_DATA_WIDTH +: M_AXI_DATA_WIDTH];
            assign m_axi_wstrb  = r_wstrb_buffer[r_beat_index[PTR_WIDTH-1:0]*M_STRB_WIDTH +: M_STRB_WIDTH];
            assign m_axi_wlast  = r_wlast_buffered && last_beat;
            assign m_axi_wuser  = r_wuser_buffer;

        end else begin : gen_w_upsize
            // Upsize: Accumulate narrow beats into wide beats

            logic [M_AXI_DATA_WIDTH-1:0] r_wdata_buffer;
            logic [M_STRB_WIDTH-1:0]     r_wstrb_buffer;
            logic [AXI_USER_WIDTH-1:0]   r_wuser_buffer;
            logic [PTR_WIDTH-1:0]        r_write_beat_ptr;
            logic                        r_wlast_buffered;
            logic                        r_buffer_full;

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    r_wdata_buffer <= '0;
                    r_wstrb_buffer <= '0;
                    r_wuser_buffer <= '0;
                    r_write_beat_ptr <= '0;
                    r_wlast_buffered <= 1'b0;
                    r_buffer_full <= 1'b0;
                end else begin
                    // Handle slave-side accumulation and master-side transmission
                    logic accepting_new_beat;
                    logic sending_master_beat;
                    logic buffer_completing;  // Buffer fills or gets last beat

                    accepting_new_beat = int_w_valid && int_w_ready;
                    sending_master_beat = m_axi_wvalid && m_axi_wready;
                    buffer_completing = accepting_new_beat && (r_write_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || int_wlast);

                    if (accepting_new_beat) begin
                        // Accumulate data into buffer
                        r_wdata_buffer[r_write_beat_ptr*S_AXI_DATA_WIDTH +: S_AXI_DATA_WIDTH] <= int_wdata;
                        r_wstrb_buffer[r_write_beat_ptr*S_STRB_WIDTH +: S_STRB_WIDTH] <= int_wstrb;
                        r_wuser_buffer <= int_wuser;
                        r_wlast_buffered <= int_wlast;

                        if (r_write_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || int_wlast) begin
                            // Buffer will be full after this beat
                            r_write_beat_ptr <= '0;
                            // Set buffer_full regardless of current transmission state
                            // If we're completing a NEW buffer, it must be marked full
                            r_buffer_full <= 1'b1;
                        end else begin
                            r_write_beat_ptr <= r_write_beat_ptr + 1'b1;
                            // Clear buffer_full if master accepted previous beat
                            if (sending_master_beat) begin
                                r_buffer_full <= 1'b0;
                            end
                        end
                    end else if (sending_master_beat && !buffer_completing) begin
                        // Buffer sent to master, clear full flag
                        // But only if we're not simultaneously completing a new buffer
                        r_buffer_full <= 1'b0;
                    end
                end
            )


            assign int_w_ready  = !r_buffer_full || (m_axi_wvalid && m_axi_wready);
            assign m_axi_wvalid = r_buffer_full;
            assign m_axi_wdata  = r_wdata_buffer;
            assign m_axi_wstrb  = r_wstrb_buffer;
            assign m_axi_wuser  = r_wuser_buffer;
            assign m_axi_wlast  = r_wlast_buffered;
        end
    endgenerate

    //==========================================================================
    // Write Response Channel (Pass-Through)
    //==========================================================================

    assign int_bid    = m_axi_bid;
    assign int_bresp  = m_axi_bresp;
    assign int_buser  = m_axi_buser;
    assign int_b_valid = m_axi_bvalid;
    assign m_axi_bready = int_b_ready;

endmodule
