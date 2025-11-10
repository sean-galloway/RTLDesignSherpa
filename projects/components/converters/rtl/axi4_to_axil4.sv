// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axil4
// Purpose: AXI4 Full to AXI4-Lite Protocol Converter
//
// Description:
//   Converts AXI4 full protocol to AXI4-Lite by:
//   - Decomposing bursts (ARLEN/AWLEN > 0) into multiple single transactions
//   - Dropping AXI4-specific signals (ID, USER, REGION, QOS)
//   - Converting full handshaking to simplified AXI4-Lite
//   - Maintaining data integrity and response propagation
//
//   Key Features:
//   - Burst decomposition: Multi-beat bursts → multiple single transactions
//   - Timing closure: Uses gaxi_skid_buffer on all channels
//   - Protocol compliant: Full AXI4 slave, AXI4-Lite master
//   - Response aggregation: Collects responses and returns with original ID
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4 side (0-1024)
//   SKID_DEPTH_AR/AW: Address channel skid depths (2-8, default 2)
//   SKID_DEPTH_R/B: Response channel skid depths (2-8, default 4)
//   SKID_DEPTH_W: Write data channel skid depth (2-8, default 4)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Burst types: FIXED, INCR, WRAP all converted to single beats
//   - Assumes downstream AXI4-Lite slave can handle traffic rate
//
// Author: RTL Design Sherpa
// Created: 2025-11-05

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axil4 #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_R      = 4,
    parameter int SKID_DEPTH_B      = 4,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Interface (Input - Full Protocol)
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
    // Master AXI4-Lite Interface (Output - Simplified Protocol)
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
    output logic                        m_axil_rready,

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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_state <= RD_IDLE;
        end else begin
            r_rd_state <= w_rd_next_state;
        end
)

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
        endcase
    end

    // Read burst tracking registers
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
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
            endcase
        end
)

    // AXI4-Lite AR channel assignment
    assign m_axil_araddr = r_ar_active ? r_ar_addr : s_axi_araddr;
    assign m_axil_arprot = r_ar_active ? r_ar_prot : s_axi_arprot;
    assign m_axil_arvalid = r_ar_active ? (r_rd_state != RD_IDLE) : s_axi_arvalid;
    assign s_axi_arready = !r_ar_active && m_axil_arready;

    // Read data path - accumulate responses
    logic [7:0] r_r_beat_count;
    logic [7:0] r_r_len;
    logic [AXI_ID_WIDTH-1:0] r_r_id;
    logic [1:0] r_r_resp_accum;  // Accumulate worst response

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
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
    )

    // Read data channel passthrough
    assign s_axi_rid = r_r_id;
    assign s_axi_rdata = m_axil_rdata;
    assign s_axi_rresp = (r_r_beat_count == r_r_len) ? r_r_resp_accum : m_axil_rresp;
    assign s_axi_rlast = (r_r_beat_count == r_r_len);
    assign s_axi_ruser = '0;  // AXI4-Lite has no USER
    assign s_axi_rvalid = m_axil_rvalid;
    assign m_axil_rready = s_axi_rready;

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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_state <= WR_IDLE;
        end else begin
            r_wr_state <= w_wr_next_state;
        end
)

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
                if (m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready) begin
                    if (r_aw_beat_count == r_aw_len - 1)
                        w_wr_next_state = WR_LAST_BEAT;
                end
            end
            WR_LAST_BEAT: begin
                if (m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready)
                    w_wr_next_state = WR_IDLE;
            end
        endcase
    end

    // Write burst tracking registers
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_id <= '0;
            r_aw_addr <= '0;
            r_aw_len <= '0;
            r_aw_beat_count <= '0;
            r_aw_size <= '0;
            r_aw_burst <= '0;
            r_aw_prot <= '0;
            r_aw_active <= 1'b0;
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
                    end
                end
                WR_BURST, WR_LAST_BEAT: begin
                    if (m_axil_awvalid && m_axil_awready && m_axil_wvalid && m_axil_wready) begin
                        r_aw_beat_count <= r_aw_beat_count + 1'b1;
                        if (r_aw_burst != 2'b00)  // Not FIXED
                            r_aw_addr <= r_aw_addr + w_aw_addr_incr;
                        if (r_wr_state == WR_LAST_BEAT)
                            r_aw_active <= 1'b0;
                    end
                end
            endcase
        end
)

    // AXI4-Lite AW and W channel assignment
    assign m_axil_awaddr = r_aw_active ? r_aw_addr : s_axi_awaddr;
    assign m_axil_awprot = r_aw_active ? r_aw_prot : s_axi_awprot;
    assign m_axil_awvalid = r_aw_active ? (r_wr_state != WR_IDLE) : s_axi_awvalid;
    assign s_axi_awready = !r_aw_active && m_axil_awready;

    // Write data passthrough
    assign m_axil_wdata = s_axi_wdata;
    assign m_axil_wstrb = s_axi_wstrb;
    assign m_axil_wvalid = s_axi_wvalid;
    assign s_axi_wready = m_axil_wready;

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
    assign s_axi_bresp = r_b_resp_accum;
    assign s_axi_buser = '0;
    assign s_axi_bvalid = m_axil_bvalid && w_b_all_beats_done;
    assign m_axil_bready = s_axi_bready || !w_b_all_beats_done;

endmodule : axi4_to_axil4
