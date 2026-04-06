// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axil4_to_axi4_rd -- pure combinational passthrough
// Verifies address/data passthrough, default field assignment, handshake forwarding

`include "reset_defs.svh"

module formal_axil4_to_axi4_rd #(
    parameter int AXI_ID_WIDTH   = 4,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1
) (
    input logic                        aclk,
    input logic                        aresetn,

    // Slave AXI4-Lite AR channel (free inputs)
    input logic [AXI_ADDR_WIDTH-1:0]   s_axil_araddr,
    input logic [2:0]                  s_axil_arprot,
    input logic                        s_axil_arvalid,

    // Master AXI4 AR channel (free input)
    input logic                        m_axi_arready,

    // Master AXI4 R channel (free inputs)
    input logic [AXI_ID_WIDTH-1:0]     m_axi_rid,
    input logic [AXI_DATA_WIDTH-1:0]   m_axi_rdata,
    input logic [1:0]                  m_axi_rresp,
    input logic                        m_axi_rlast,
    input logic [AXI_USER_WIDTH-1:0]   m_axi_ruser,
    input logic                        m_axi_rvalid,

    // Slave AXI4-Lite R channel (free input)
    input logic                        s_axil_rready
);

    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8;
    localparam int SIZE_VAL   = $clog2(STRB_WIDTH);
    localparam int DEFAULT_ID = 0;

    // DUT outputs
    logic                        s_axil_arready_o;
    logic [AXI_DATA_WIDTH-1:0]   s_axil_rdata_o;
    logic [1:0]                  s_axil_rresp_o;
    logic                        s_axil_rvalid_o;

    logic [AXI_ID_WIDTH-1:0]     m_axi_arid_o;
    logic [AXI_ADDR_WIDTH-1:0]   m_axi_araddr_o;
    logic [7:0]                  m_axi_arlen_o;
    logic [2:0]                  m_axi_arsize_o;
    logic [1:0]                  m_axi_arburst_o;
    logic                        m_axi_arlock_o;
    logic [3:0]                  m_axi_arcache_o;
    logic [2:0]                  m_axi_arprot_o;
    logic [3:0]                  m_axi_arqos_o;
    logic [3:0]                  m_axi_arregion_o;
    logic [AXI_USER_WIDTH-1:0]   m_axi_aruser_o;
    logic                        m_axi_arvalid_o;
    logic                        m_axi_rready_o;

    axil4_to_axi4_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .DEFAULT_ID     (DEFAULT_ID),
        .DEFAULT_REGION (0),
        .DEFAULT_QOS    (0),
        .SKID_DEPTH_AR  (2),
        .SKID_DEPTH_R   (4)
    ) dut (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // Slave AXI4-Lite
        .s_axil_araddr   (s_axil_araddr),
        .s_axil_arprot   (s_axil_arprot),
        .s_axil_arvalid  (s_axil_arvalid),
        .s_axil_arready  (s_axil_arready_o),
        .s_axil_rdata    (s_axil_rdata_o),
        .s_axil_rresp    (s_axil_rresp_o),
        .s_axil_rvalid   (s_axil_rvalid_o),
        .s_axil_rready   (s_axil_rready),

        // Master AXI4
        .m_axi_arid      (m_axi_arid_o),
        .m_axi_araddr    (m_axi_araddr_o),
        .m_axi_arlen     (m_axi_arlen_o),
        .m_axi_arsize    (m_axi_arsize_o),
        .m_axi_arburst   (m_axi_arburst_o),
        .m_axi_arlock    (m_axi_arlock_o),
        .m_axi_arcache   (m_axi_arcache_o),
        .m_axi_arprot    (m_axi_arprot_o),
        .m_axi_arqos     (m_axi_arqos_o),
        .m_axi_arregion  (m_axi_arregion_o),
        .m_axi_aruser    (m_axi_aruser_o),
        .m_axi_arvalid   (m_axi_arvalid_o),
        .m_axi_arready   (m_axi_arready),
        .m_axi_rid       (m_axi_rid),
        .m_axi_rdata     (m_axi_rdata),
        .m_axi_rresp     (m_axi_rresp),
        .m_axi_rlast     (m_axi_rlast),
        .m_axi_ruser     (m_axi_ruser),
        .m_axi_rvalid    (m_axi_rvalid),
        .m_axi_rready    (m_axi_rready_o)
    );

    // =========================================================================
    // Past-valid counter (combinational module, but clock-based assertions)
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // =========================================================================
    // P1: Address passthrough
    // =========================================================================
    always @(*) begin
        ap_addr_passthrough: assert (m_axi_araddr_o == s_axil_araddr);
    end

    // =========================================================================
    // P2: Prot passthrough
    // =========================================================================
    always @(*) begin
        ap_prot_passthrough: assert (m_axi_arprot_o == s_axil_arprot);
    end

    // =========================================================================
    // P3: Valid passthrough
    // =========================================================================
    always @(*) begin
        ap_valid_passthrough: assert (m_axi_arvalid_o == s_axil_arvalid);
    end

    // =========================================================================
    // P4: Ready passthrough
    // =========================================================================
    always @(*) begin
        ap_ready_passthrough: assert (s_axil_arready_o == m_axi_arready);
    end

    // =========================================================================
    // P5: ARLEN always 0 (single beat)
    // =========================================================================
    always @(*) begin
        ap_arlen_zero: assert (m_axi_arlen_o == 8'd0);
    end

    // =========================================================================
    // P6: ARBURST always INCR (2'b01)
    // =========================================================================
    always @(*) begin
        ap_arburst_incr: assert (m_axi_arburst_o == 2'b01);
    end

    // =========================================================================
    // P7: ARID == DEFAULT_ID
    // =========================================================================
    always @(*) begin
        ap_arid_default: assert (m_axi_arid_o == AXI_ID_WIDTH'(DEFAULT_ID));
    end

    // =========================================================================
    // P8: ARSIZE correct for data width
    // =========================================================================
    always @(*) begin
        ap_arsize_correct: assert (m_axi_arsize_o == 3'(SIZE_VAL));
    end

    // =========================================================================
    // P9: R data passthrough
    // =========================================================================
    always @(*) begin
        ap_rdata_passthrough: assert (s_axil_rdata_o == m_axi_rdata);
    end

    // =========================================================================
    // P10: R resp passthrough
    // =========================================================================
    always @(*) begin
        ap_rresp_passthrough: assert (s_axil_rresp_o == m_axi_rresp);
    end

    // =========================================================================
    // P11: R valid passthrough
    // =========================================================================
    always @(*) begin
        ap_rvalid_passthrough: assert (s_axil_rvalid_o == m_axi_rvalid);
    end

    // =========================================================================
    // P12: R ready passthrough
    // =========================================================================
    always @(*) begin
        ap_rready_passthrough: assert (m_axi_rready_o == s_axil_rready);
    end

    // =========================================================================
    // P13: ARLOCK always 0
    // =========================================================================
    always @(*) begin
        ap_arlock_zero: assert (m_axi_arlock_o == 1'b0);
    end

    // =========================================================================
    // P14: ARCACHE always bufferable (4'b0011)
    // =========================================================================
    always @(*) begin
        ap_arcache_default: assert (m_axi_arcache_o == 4'b0011);
    end

    // =========================================================================
    // P15: ARUSER always 0
    // =========================================================================
    always @(*) begin
        ap_aruser_zero: assert (m_axi_aruser_o == '0);
    end

    // =========================================================================
    // Cover: AR handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_ar_handshake: cover (s_axil_arvalid && s_axil_arready_o);
    end

    // =========================================================================
    // Cover: R handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_r_handshake: cover (s_axil_rvalid_o && s_axil_rready);
    end

endmodule
