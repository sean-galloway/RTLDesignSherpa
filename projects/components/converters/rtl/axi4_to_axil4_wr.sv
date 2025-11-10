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
//   SKID_DEPTH_AW: Address channel skid depth (2-8, default 2)
//   SKID_DEPTH_W: Write data channel skid depth (2-8, default 4)
//   SKID_DEPTH_B: Response channel skid depth (2-8, default 4)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Burst types: FIXED, INCR, WRAP all converted to single beats
//   - Write-only: No read path support
//
// Author: RTL Design Sherpa
// Created: 2025-11-05

`timescale 1ns / 1ps

module axi4_to_axil4_wr #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 4,

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
    logic [AXI_ID_WIDTH-1:0]     r_aw_id;
    logic [AXI_ADDR_WIDTH-1:0]   r_aw_addr;
    logic [7:0]                  r_aw_len;
    logic [7:0]                  r_aw_beat_count;
    logic [2:0]                  r_aw_size;
    logic [1:0]                  r_aw_burst;
    logic [2:0]                  r_aw_prot;
    logic                        r_aw_active;
    logic                        r_aw_sent;    // AW beat sent, waiting for W

    // Address increment calculation
    logic [AXI_ADDR_WIDTH-1:0] w_aw_addr_incr;
    assign w_aw_addr_incr = (1 << r_aw_size);

    // Write state machine
    typedef enum logic [1:0] {
        WR_IDLE       = 2'b00,
        WR_BURST      = 2'b01,
        WR_LAST_BEAT  = 2'b10
    } wr_state_t;

    wr_state_t r_wr_state, w_wr_next_state;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_wr_state <= WR_IDLE;
        end else begin
            r_wr_state <= w_wr_next_state;
        end
    end

    // Write next state logic
    always_comb begin
        w_wr_next_state = r_wr_state;
        case (r_wr_state)
            WR_IDLE: begin
                if (s_axi_awvalid && s_axi_awready) begin
                    if (s_axi_awlen == 0)
                        w_wr_next_state = WR_IDLE;
                    else
                        w_wr_next_state = WR_BURST;
                end
            end
            WR_BURST: begin
                // Transition when beat completes (either AW+W together, or W after AW)
                if ((m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready) ||
                    (r_aw_sent && m_axil_wvalid && m_axil_wready)) begin
                    if (r_aw_beat_count == r_aw_len - 1)
                        w_wr_next_state = WR_LAST_BEAT;
                end
            end
            WR_LAST_BEAT: begin
                // Transition when beat completes (either AW+W together, or W after AW)
                if ((m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready) ||
                    (r_aw_sent && m_axil_wvalid && m_axil_wready))
                    w_wr_next_state = WR_IDLE;
            end
            default: w_wr_next_state = WR_IDLE;
        endcase
    end

    // Write burst tracking registers
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_aw_id <= '0;
            r_aw_addr <= '0;
            r_aw_len <= '0;
            r_aw_beat_count <= '0;
            r_aw_size <= '0;
            r_aw_burst <= '0;
            r_aw_prot <= '0;
            r_aw_active <= 1'b0;
            r_aw_sent <= 1'b0;
        end else begin
            case (r_wr_state)
                WR_IDLE: begin
                    if (s_axi_awvalid && s_axi_awready) begin
                        r_aw_id <= s_axi_awid;
                        r_aw_addr <= s_axi_awaddr;
                        r_aw_len <= s_axi_awlen;
                        r_aw_beat_count <= 8'd0;
                        r_aw_size <= s_axi_awsize;
                        r_aw_burst <= s_axi_awburst;
                        r_aw_prot <= s_axi_awprot;
                        r_aw_active <= (s_axi_awlen > 0);
                    end else begin
                        r_aw_active <= 1'b0;  // Clear when idle and not accepting new AW
                    end
                    r_aw_sent <= 1'b0;
                end
                WR_BURST, WR_LAST_BEAT: begin
                    // Track AW/W completion for this beat
                    if (m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready) begin
                        // Both AW and W complete together
                        r_aw_beat_count <= r_aw_beat_count + 1'b1;
                        if (r_aw_burst != 2'b00)  // Not FIXED
                            r_aw_addr <= r_aw_addr + w_aw_addr_incr;
                        if (r_wr_state == WR_LAST_BEAT)
                            r_aw_active <= 1'b0;
                        r_aw_sent <= 1'b0;  // Ready for next beat
                    end else if (m_axil_awvalid && m_axil_awready) begin
                        // AW completes but W doesn't
                        r_aw_sent <= 1'b1;
                    end else if (r_aw_sent && m_axil_wvalid && m_axil_wready) begin
                        // W completes after AW
                        r_aw_beat_count <= r_aw_beat_count + 1'b1;
                        if (r_aw_burst != 2'b00)  // Not FIXED
                            r_aw_addr <= r_aw_addr + w_aw_addr_incr;
                        if (r_wr_state == WR_LAST_BEAT)
                            r_aw_active <= 1'b0;
                        r_aw_sent <= 1'b0;
                    end
                end
                default: begin
                    r_aw_sent <= 1'b0;
                end
            endcase
        end
    end

    // AXI4-Lite AW and W channel assignment
    // For bursts (awlen>0): Don't pass through, let FSM handle all beats
    // For single beats (awlen==0): Pass through directly for efficiency
    assign m_axil_awaddr = r_aw_active ? r_aw_addr : s_axi_awaddr;
    assign m_axil_awprot = r_aw_active ? r_aw_prot : s_axi_awprot;
    assign m_axil_awvalid = r_aw_active ? (r_wr_state != WR_IDLE && !r_aw_sent) :
                            (s_axi_awvalid && (s_axi_awlen == 0));
    // For bursts, accept AW immediately into registers (don't wait for AXIL ready)
    // For single beats, tie to AXIL ready for passthrough
    assign s_axi_awready = !r_aw_active &&
                           ((s_axi_awlen == 0) ? m_axil_awready : 1'b1);

    // Write data control with burst synchronization
    // W channel must be synchronized with AW FSM for burst decomposition
    assign m_axil_wdata = s_axi_wdata;
    assign m_axil_wstrb = s_axi_wstrb;
    // For bursts: W passthrough, but only consume when:
    //   - AW is handshaking this cycle, OR
    //   - AW has already been sent for this beat (r_aw_sent)
    // This ensures AW completes before or with W, never after
    // For single beats: Pass through directly
    assign m_axil_wvalid = s_axi_wvalid;
    assign s_axi_wready = r_aw_active ? (m_axil_wready && (r_aw_sent || (m_axil_awvalid && m_axil_awready))) :
                          m_axil_wready;

    // Write response path - accumulate responses
    logic [7:0] r_b_beat_count;
    logic [7:0] r_b_len;
    logic [AXI_ID_WIDTH-1:0] r_b_id;
    logic [1:0] r_b_resp_accum;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
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
    end

    // Write response channel - only generate response after all beats complete
    logic w_b_all_beats_done;
    assign w_b_all_beats_done = (r_b_beat_count == r_b_len);

    assign s_axi_bid = r_b_id;
    assign s_axi_bresp = r_b_resp_accum;
    assign s_axi_buser = '0;
    assign s_axi_bvalid = m_axil_bvalid && w_b_all_beats_done;
    assign m_axil_bready = s_axi_bready || !w_b_all_beats_done;

endmodule : axi4_to_axil4_wr
