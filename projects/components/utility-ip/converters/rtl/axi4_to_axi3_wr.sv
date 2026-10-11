// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axi3_wr
// Purpose: AXI4 Full to AXI3 Protocol Converter (WRITE-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI3 for WRITE path only by:
//   - Passing AW through (AXI4 AWLEN truncated to 4 bits, AWLOCK mapped
//     from 1 bit to 2 bits, QOS/REGION dropped)
//   - Stamping each W beat with the owning AWID on m_axi3_wid
//   - Forwarding WDATA, WSTRB, WLAST, and WUSER unchanged
//   - Buffering early W beats that arrive before the matching AW handshake
//     (one full AXI3 burst of storage)
//   - Passing B responses through with ID preserved
//
//   Standalone write-only implementation. For read conversion, use
//   axi4_to_axi3_rd.sv.
//
//   Key Features:
//   - Write-only: AW, W, B channels only
//   - Per-burst WID stamping so an AXI3 slave can demux by WID
//   - Early-W buffering for AXI4 masters that send W before AW
//   - Single-burst W path ordering (AWs are queued but W beats are issued
//     for one burst at a time)
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4/AXI3 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4/AXI3 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - v1 supports AXI4 write bursts up to 16 beats (AWLEN <= 15)
//   - Write-only: No read path support
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axi3_wr #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Write Interface (Input - Full Protocol)
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
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
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
    // Master AXI3 Write Interface (Output - AXI3 Protocol)
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi3_awaddr,
    output logic [3:0]                  m_axi3_awlen,
    output logic [2:0]                  m_axi3_awsize,
    output logic [1:0]                  m_axi3_awburst,
    output logic [1:0]                  m_axi3_awlock,
    output logic [3:0]                  m_axi3_awcache,
    output logic [2:0]                  m_axi3_awprot,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_awuser,
    output logic                        m_axi3_awvalid,
    input  logic                        m_axi3_awready,

    // Write Data Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_wid,
    output logic [AXI_DATA_WIDTH-1:0]   m_axi3_wdata,
    output logic [STRB_WIDTH-1:0]       m_axi3_wstrb,
    output logic                        m_axi3_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_wuser,
    output logic                        m_axi3_wvalid,
    input  logic                        m_axi3_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi3_bid,
    input  logic [1:0]                  m_axi3_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi3_buser,
    input  logic                        m_axi3_bvalid,
    output logic                        m_axi3_bready
);

    //==========================================================================
    // Local Parameters and Typedefs
    //==========================================================================

    localparam int Axi3MaxBeats = 16;
    localparam int AwQueueDepth = 4;
    localparam int WBufferDepth = Axi3MaxBeats;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]   id;
        logic [AXI_ADDR_WIDTH-1:0] addr;
        logic [3:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic                      lock;
        logic [3:0]                cache;
        logic [2:0]                prot;
        logic [AXI_USER_WIDTH-1:0] user;
    } aw_req_t;

    typedef struct packed {
        logic [AXI_DATA_WIDTH-1:0] data;
        logic [STRB_WIDTH-1:0]     strb;
        logic                      last;
        logic [AXI_USER_WIDTH-1:0] user;
    } w_beat_t;

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // AW queue and active burst state
    aw_req_t aw_queue[$:AwQueueDepth-1];
    aw_req_t active_aw;
    logic    active_valid;
    logic [4:0] w_forwarded;

    // W buffering
    w_beat_t w_buffer[$:WBufferDepth-1];

    // Convenience aliases
    logic w_handshake;
    logic m_w_handshake;

    //==========================================================================
    // Burst Length Assertion
    //==========================================================================

    // v1 supports AXI4 bursts up to 16 beats. Longer bursts would require
    // chopping, which is not implemented in this version.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // No check during reset
        end else begin
            if (s_axi_awvalid && s_axi_awready && (s_axi_awlen > 8'd15))
                $error("ASSERT_A3_WR_LEN16: AXI4 write burst length %0d exceeds AXI3 maximum of 16 beats", s_axi_awlen);
        end
    )

    //==========================================================================
    // Write Address Channel Pass-Through
    //==========================================================================

    assign s_axi_awready = (aw_queue.size() < AwQueueDepth) && m_axi3_awready;
    assign m_axi3_awvalid = s_axi_awvalid && (aw_queue.size() < AwQueueDepth);

    assign m_axi3_awid    = s_axi_awid;
    assign m_axi3_awaddr  = s_axi_awaddr;
    assign m_axi3_awlen   = s_axi_awlen[3:0];
    assign m_axi3_awsize  = s_axi_awsize;
    assign m_axi3_awburst = s_axi_awburst;
    assign m_axi3_awlock  = s_axi_awlock ? 2'b10 : 2'b00;
    assign m_axi3_awcache = s_axi_awcache;
    assign m_axi3_awprot  = s_axi_awprot;
    assign m_axi3_awuser  = s_axi_awuser;

    //==========================================================================
    // Write Response Channel Pass-Through
    //==========================================================================

    assign s_axi_bid    = m_axi3_bid;
    assign s_axi_bresp  = m_axi3_bresp;
    assign s_axi_buser  = m_axi3_buser;
    assign s_axi_bvalid = m_axi3_bvalid;
    assign m_axi3_bready = s_axi_bready;

    //==========================================================================
    // Write Data Channel: Buffering + WID Stamping
    //==========================================================================

    assign w_handshake   = s_axi_wvalid && s_axi_wready;
    assign m_w_handshake = m_axi3_wvalid && m_axi3_wready;

    // Accept W beats as long as the early-W buffer has space. A well-behaved
    // AXI4 master will not send more than the active burst length; the buffer
    // itself bounds how far early W can run ahead of AW.
    assign s_axi_wready = (w_buffer.size() < WBufferDepth);

    // Forward buffered W beats only when an AW is active (so WID is known).
    assign m_axi3_wid   = active_aw.id;
    assign m_axi3_wdata = w_buffer[0].data;
    assign m_axi3_wstrb = w_buffer[0].strb;
    assign m_axi3_wlast = w_buffer[0].last;
    assign m_axi3_wuser = w_buffer[0].user;
    assign m_axi3_wvalid = active_valid && (w_buffer.size() > 0);

    // Early-W buffer overflow assertion. Fires when a W beat arrives while the
    // buffer is already full, which means the AXI4 master sent more than one
    // full burst ahead of the matching AW.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // No check during reset
        end else begin
            if (s_axi_wvalid && (w_buffer.size() >= WBufferDepth))
                $error("ASSERT_A3_WR_WBUF_OVFL: W beat dropped; early-W buffer overflow (depth=%0d)", WBufferDepth);
        end
    )

    //==========================================================================
    // Sequential State: AW Queue, Burst Activation, and W Buffer
    //==========================================================================

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            aw_queue.delete();
            w_buffer.delete();
            active_valid <= 1'b0;
            active_aw    <= '0;
            w_forwarded  <= '0;
        end else begin
            // Accept a new slave AW into the queue.
            if (s_axi_awvalid && s_axi_awready) begin
                aw_req_t push;
                push.id    = s_axi_awid;
                push.addr  = s_axi_awaddr;
                push.len   = s_axi_awlen[3:0];
                push.size  = s_axi_awsize;
                push.burst = s_axi_awburst;
                push.lock  = s_axi_awlock;
                push.cache = s_axi_awcache;
                push.prot  = s_axi_awprot;
                push.user  = s_axi_awuser;
                aw_queue.push_back(push);
            end

            // Buffer an incoming W beat.
            if (w_handshake) begin
                w_beat_t beat;
                beat.data = s_axi_wdata;
                beat.strb = s_axi_wstrb;
                beat.last = s_axi_wlast;
                beat.user = s_axi_wuser;
                w_buffer.push_back(beat);
            end

            // Forward a buffered W beat to the AXI3 master.
            if (m_w_handshake) begin
                w_beat_t fwd;
                fwd = w_buffer[0];
                w_buffer.pop_front();
                w_forwarded <= w_forwarded + 1'b1;
                if (fwd.last) begin
                    active_valid <= 1'b0;
                end
            end

            // Activate the next queued burst when idle.
            if (!active_valid && (aw_queue.size() > 0)) begin
                active_aw    <= aw_queue.pop_front();
                active_valid <= 1'b1;
                w_forwarded  <= '0;
            end
        end
    )

endmodule : axi4_to_axi3_wr
