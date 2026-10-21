// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axil4_wr
// Purpose: AXI4 Full to AXI4-Lite Protocol Converter (WRITE-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI4-Lite for WRITE path only by:
//   - Decomposing write bursts (AWLEN > 0) into multiple single transactions
//   - Dropping AXI4-specific signals (ID, USER, REGION, QOS)
//   - Converting full handshaking to simplified AXI4-Lite
//   - Maintaining data integrity and response propagation
//
//   Standalone write-only implementation. For read conversion, use
//   axi4_to_axil4_rd.sv.
//
//   Key Features:
//   - Write-only: AW, W, B channels only
//   - Burst decomposition: Multi-beat bursts → multiple single transactions
//   - Response aggregation: Collects responses and returns with original ID
//   - Protocol compliant: Full AXI4 slave, AXI4-Lite master
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Burst types: FIXED, INCR, WRAP all converted to single beats
//   - Write-only: No read path support
//
// Author: RTL Design Sherpa
// Created: 2025-11-05

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axil4_wr #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)



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
    // Master AXI4-Lite Write Interface (Output - Simplified Protocol)
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]                  m_axil_awprot,
    output logic                        m_axil_awvalid,
    input  logic                        m_axil_awready,

    // Write Data Channel
    output logic [AXI_DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [STRB_WIDTH-1:0]       m_axil_wstrb,
    output logic                        m_axil_wvalid,
    input  logic                        m_axil_wready,

    // Write Response Channel
    input  logic [1:0]                  m_axil_bresp,
    input  logic                        m_axil_bvalid,
    output logic                        m_axil_bready
);

    //==========================================================================
    // Write Path: Burst Decomposition
    //==========================================================================

    // Write burst tracker
    logic [AXI_ADDR_WIDTH-1:0]   r_aw_addr;
    logic [7:0]                  r_aw_len;
    logic [7:0]                  r_aw_beat_count;
    logic [2:0]                  r_aw_size;
    logic [1:0]                  r_aw_burst;
    logic [2:0]                  r_aw_prot;
    logic                        r_aw_active;
    logic                        r_aw_sent;    // this beat's AXI4-Lite AW is done, waiting for its W

    // Address increment calculation
    logic [AXI_ADDR_WIDTH-1:0] w_aw_addr_incr;
    assign w_aw_addr_incr = (1 << r_aw_size);

    // WRAP wraps inside an aligned (len+1) * (1 << size) byte window: the
    // low bits advance and carry back to the window base instead of running
    // past it. Without this a WRAP burst is written as INCR and the beats
    // that should fold back land outside the window entirely.
    logic [AXI_ADDR_WIDTH-1:0] w_aw_wrap_mask;
    logic [AXI_ADDR_WIDTH-1:0] w_aw_next_addr;
    assign w_aw_wrap_mask = (({{(AXI_ADDR_WIDTH-8){1'b0}}, r_aw_len} + 1)
                             << r_aw_size) - 1;
    assign w_aw_next_addr =
        (r_aw_burst == 2'b10)
            ? ((r_aw_addr & ~w_aw_wrap_mask) |
               ((r_aw_addr + w_aw_addr_incr) & w_aw_wrap_mask))
            : (r_aw_addr + w_aw_addr_incr);

    // Write sequencing. Every AW, single-beat or burst, is taken into the
    // r_aw_* registers and then issued as AXI4-Lite beats, one at a time.
    // Within a beat the AXI4-Lite AW and W handshakes are independent: the
    // beat is done once both have happened, in either order or together.
    //
    // As the AXI4-Lite master this block must not wait for AWREADY before
    // asserting WVALID (AXI A3.3.1), because the slave may wait for WVALID
    // before asserting AWREADY -- an AXI CDMA register slave does, and the
    // older version, which forwarded a beat's W only with or after its AW
    // handshake and passed single beats' AWREADY straight through, deadlocked
    // against it on the board (bridge BUG-020). W passes only for a
    // registered burst, so a W beat can never pair with the wrong AW (the
    // orphan-W hazard of the old passthrough leg cannot arise).
    //
    // One AXI write burst in flight at a time: r_wr_outstanding is set when
    // the AW is taken and cleared when its B is handed to the master; the
    // response path below keeps a single-entry record of it.
    logic r_w_sent;     // this beat's AXI4-Lite W is done, waiting for its AW
    logic w_axil_aw_hs, w_axil_w_hs, w_beat_aw_done, w_beat_w_done, w_beat_done;
    logic w_last_beat;
    assign w_axil_aw_hs   = m_axil_awvalid && m_axil_awready;
    assign w_axil_w_hs    = m_axil_wvalid && m_axil_wready;
    assign w_beat_aw_done = r_aw_sent || w_axil_aw_hs;
    assign w_beat_w_done  = r_w_sent  || w_axil_w_hs;
    assign w_beat_done    = r_aw_active && w_beat_aw_done && w_beat_w_done;
    assign w_last_beat    = (r_aw_beat_count == r_aw_len);

    logic r_wr_outstanding;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_outstanding <= 1'b0;
        end else if (s_axi_bvalid && s_axi_bready) begin
            // A combinational AXIL response can return B in the same cycle
            // the AW is taken; clear wins only because awready is low while
            // set, so the two cannot coincide for one burst.
            r_wr_outstanding <= 1'b0;
        end else if (s_axi_awvalid && s_axi_awready) begin
            r_wr_outstanding <= 1'b1;
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_addr       <= '0;
            r_aw_len        <= '0;
            r_aw_beat_count <= '0;
            r_aw_size       <= '0;
            r_aw_burst      <= '0;
            r_aw_prot       <= '0;
            r_aw_active     <= 1'b0;
            r_aw_sent       <= 1'b0;
            r_w_sent        <= 1'b0;
        end else if (s_axi_awvalid && s_axi_awready) begin
            r_aw_addr       <= s_axi_awaddr;
            r_aw_len        <= s_axi_awlen;
            r_aw_beat_count <= 8'd0;
            r_aw_size       <= s_axi_awsize;
            r_aw_burst      <= s_axi_awburst;
            r_aw_prot       <= s_axi_awprot;
            r_aw_active     <= 1'b1;
            r_aw_sent       <= 1'b0;
            r_w_sent        <= 1'b0;
        end else if (w_beat_done) begin
            r_aw_beat_count <= r_aw_beat_count + 1'b1;
            if (r_aw_burst != 2'b00)  // not FIXED
                r_aw_addr <= w_aw_next_addr;
            if (w_last_beat)
                r_aw_active <= 1'b0;
            r_aw_sent <= 1'b0;
            r_w_sent  <= 1'b0;
        end else begin
            if (w_axil_aw_hs) r_aw_sent <= 1'b1;
            if (w_axil_w_hs)  r_w_sent  <= 1'b1;
        end
    )

    assign s_axi_awready  = !r_aw_active && !r_wr_outstanding;
    assign m_axil_awaddr  = r_aw_addr;
    assign m_axil_awprot  = r_aw_prot;
    assign m_axil_awvalid = r_aw_active && !r_aw_sent;

    assign m_axil_wdata  = s_axi_wdata;
    assign m_axil_wstrb  = s_axi_wstrb;
    assign m_axil_wvalid = r_aw_active && !r_w_sent && s_axi_wvalid;
    assign s_axi_wready  = r_aw_active && !r_w_sent && m_axil_wready;

    // Write response path - accumulate responses
    logic [7:0] r_b_beat_count;
    logic [7:0] r_b_len;
    logic [AXI_ID_WIDTH-1:0] r_b_id;
    logic [1:0] r_b_resp_accum;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_beat_count <= '0;
            r_b_len <= '0;
            r_b_id <= '0;
            r_b_resp_accum <= 2'b00;
        end else begin
            if (s_axi_awvalid && s_axi_awready) begin
                r_b_len <= s_axi_awlen;
                r_b_id <= s_axi_awid;
                r_b_resp_accum <= 2'b00;
                r_b_beat_count <= 8'd0;
            end
            if (m_axil_bvalid && m_axil_bready) begin
                r_b_beat_count <= r_b_beat_count + 1'b1;
                if (m_axil_bresp > r_b_resp_accum)
                    r_b_resp_accum <= m_axil_bresp;
            end
        end
    )

    // Write response channel - only generate response after all beats complete
    logic w_b_all_beats_done;
    assign w_b_all_beats_done = (r_b_beat_count == r_b_len);

    assign s_axi_bid = r_b_id;
    // The accumulator is a registered fold, so at the moment B is emitted it
    // does not yet contain the final beat's own response -- the non-blocking
    // assign lands next cycle. That dropped the last beat's error at any
    // burst length, and for awlen=0 the only beat IS the last one, so every
    // single-beat write error was reported to the master as OKAY. Fold the
    // live beat in before emitting. (bresp is only sampled while bvalid,
    // which requires m_axil_bvalid, so m_axil_bresp is valid here.)
    logic [1:0] w_b_resp_worst;
    assign w_b_resp_worst = (m_axil_bresp > r_b_resp_accum) ? m_axil_bresp
                                                            : r_b_resp_accum;
    assign s_axi_bresp = w_b_resp_worst;
    assign s_axi_buser = '0;
    assign s_axi_bvalid = m_axil_bvalid && w_b_all_beats_done;
    assign m_axil_bready = s_axi_bready || !w_b_all_beats_done;

endmodule : axi4_to_axil4_wr
