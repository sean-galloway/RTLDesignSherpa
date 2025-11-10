// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axil4_rd
// Purpose: AXI4 Full to AXI4-Lite Protocol Converter (READ-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI4-Lite for READ path only by:
//   - Decomposing read bursts (ARLEN > 0) into multiple single transactions
//   - Dropping AXI4-specific signals (ID, USER, REGION, QOS)
//   - Converting full handshaking to simplified AXI4-Lite
//   - Maintaining data integrity and response propagation
//
//   Standalone read-only implementation. For write conversion, use
//   axi4_to_axil4_wr.sv.
//
//   Key Features:
//   - Read-only: AR, R channels only
//   - Burst decomposition: Multi-beat bursts → multiple single transactions
//   - Response aggregation: Collects responses and returns with original ID
//   - Protocol compliant: Full AXI4 slave, AXI4-Lite master
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4 side (0-1024)
//   SKID_DEPTH_AR: Address channel skid depth (2-8, default 2)
//   SKID_DEPTH_R: Response channel skid depth (2-8, default 4)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Burst types: FIXED, INCR, WRAP all converted to single beats
//   - Read-only: No write path support
//
// Author: RTL Design Sherpa
// Created: 2025-11-05

`timescale 1ns / 1ps

module axi4_to_axil4_rd #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Read Interface (Input - Full Protocol)
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
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //==========================================================================
    // Master AXI4-Lite Read Interface (Output - Simplified Protocol)
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                  m_axil_arprot,
    output logic                        m_axil_arvalid,
    input  logic                        m_axil_arready,

    // Read Data Channel
    input  logic [AXI_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                  m_axil_rresp,
    input  logic                        m_axil_rvalid,
    output logic                        m_axil_rready
);

    //==========================================================================
    // Read Path: Burst Decomposition
    //==========================================================================

    // Read burst tracker
    logic [AXI_ID_WIDTH-1:0]     r_ar_id;
    logic [AXI_ADDR_WIDTH-1:0]   r_ar_addr;
    logic [7:0]                  r_ar_len;
    logic [7:0]                  r_ar_beat_count;
    logic [2:0]                  r_ar_size;
    logic [1:0]                  r_ar_burst;
    logic [2:0]                  r_ar_prot;
    logic                        r_ar_active;

    // Address increment calculation
    logic [AXI_ADDR_WIDTH-1:0] w_ar_addr_incr;
    assign w_ar_addr_incr = (1 << r_ar_size);  // Byte increment per beat

    // Read state machine
    typedef enum logic [1:0] {
        RD_IDLE       = 2'b00,
        RD_BURST      = 2'b01,
        RD_LAST_BEAT  = 2'b10
    } rd_state_t;

    rd_state_t r_rd_state, w_rd_next_state;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_rd_state <= RD_IDLE;
        end else begin
            r_rd_state <= w_rd_next_state;
        end
    end

    // Read next state logic
    always_comb begin
        w_rd_next_state = r_rd_state;
        case (r_rd_state)
            RD_IDLE: begin
                if (s_axi_arvalid && s_axi_arready) begin
                    if (s_axi_arlen == 0)
                        w_rd_next_state = RD_IDLE;  // Single beat, stay idle
                    else
                        w_rd_next_state = RD_BURST;  // Start burst decomposition
                end
            end
            RD_BURST: begin
                if (m_axil_arvalid && m_axil_arready) begin
                    if (r_ar_beat_count == r_ar_len - 1)
                        w_rd_next_state = RD_LAST_BEAT;
                end
            end
            RD_LAST_BEAT: begin
                if (m_axil_arvalid && m_axil_arready)
                    w_rd_next_state = RD_IDLE;
            end
            default: w_rd_next_state = RD_IDLE;
        endcase
    end

    // Read burst tracking registers
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_ar_id <= '0;
            r_ar_addr <= '0;
            r_ar_len <= '0;
            r_ar_beat_count <= '0;
            r_ar_size <= '0;
            r_ar_burst <= '0;
            r_ar_prot <= '0;
            r_ar_active <= 1'b0;
        end else begin
            case (r_rd_state)
                RD_IDLE: begin
                    if (s_axi_arvalid && s_axi_arready) begin
                        r_ar_id <= s_axi_arid;
                        r_ar_addr <= s_axi_araddr;
                        r_ar_len <= s_axi_arlen;
                        r_ar_beat_count <= 8'd0;
                        r_ar_size <= s_axi_arsize;
                        r_ar_burst <= s_axi_arburst;
                        r_ar_prot <= s_axi_arprot;
                        r_ar_active <= (s_axi_arlen > 0);
                    end
                end
                RD_BURST, RD_LAST_BEAT: begin
                    if (m_axil_arvalid && m_axil_arready) begin
                        r_ar_beat_count <= r_ar_beat_count + 1'b1;
                        // Address increment (INCR and WRAP both increment)
                        if (r_ar_burst != 2'b00)  // Not FIXED
                            r_ar_addr <= r_ar_addr + w_ar_addr_incr;
                        if (r_rd_state == RD_LAST_BEAT)
                            r_ar_active <= 1'b0;
                    end
                end
                default: begin
                    // Do nothing for undefined states
                end
            endcase
        end
    end

    // AXI4-Lite AR channel assignment
    // For bursts (arlen>0): Don't pass through, let FSM handle all beats
    // For single beats (arlen==0): Pass through directly for efficiency
    assign m_axil_araddr = r_ar_active ? r_ar_addr : s_axi_araddr;
    assign m_axil_arprot = r_ar_active ? r_ar_prot : s_axi_arprot;
    assign m_axil_arvalid = r_ar_active ? (r_rd_state != RD_IDLE) :
                            (s_axi_arvalid && (s_axi_arlen == 0));
    // For bursts, accept AR immediately into registers (don't wait for AXIL ready)
    // For single beats, tie to AXIL ready for passthrough
    assign s_axi_arready = !r_ar_active &&
                           ((s_axi_arlen == 0) ? m_axil_arready : 1'b1);

    // Read data path - accumulate responses
    logic [7:0] r_r_beat_count;
    logic [7:0] r_r_len;
    logic [AXI_ID_WIDTH-1:0] r_r_id;
    logic [1:0] r_r_resp_accum;  // Accumulate worst response

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_r_beat_count <= '0;
            r_r_len <= '0;
            r_r_id <= '0;
            r_r_resp_accum <= 2'b00;  // OKAY
        end else begin
            // Capture burst info on first AR acceptance
            if (s_axi_arvalid && s_axi_arready) begin
                r_r_len <= s_axi_arlen;
                r_r_id <= s_axi_arid;
                r_r_resp_accum <= 2'b00;
                r_r_beat_count <= 8'd0;
            end
            // Track read data beats
            if (m_axil_rvalid && m_axil_rready) begin
                r_r_beat_count <= r_r_beat_count + 1'b1;
                // Accumulate worst response (SLVERR > DECERR > EXOKAY > OKAY)
                if (m_axil_rresp > r_r_resp_accum)
                    r_r_resp_accum <= m_axil_rresp;
            end
        end
    end

    // Read data channel passthrough
    assign s_axi_rid = r_r_id;
    assign s_axi_rdata = m_axil_rdata;
    assign s_axi_rresp = (r_r_beat_count == r_r_len) ? r_r_resp_accum : m_axil_rresp;
    assign s_axi_rlast = (r_r_beat_count == r_r_len);
    assign s_axi_ruser = '0;  // AXI4-Lite has no USER
    assign s_axi_rvalid = m_axil_rvalid;
    assign m_axil_rready = s_axi_rready;

endmodule : axi4_to_axil4_rd
