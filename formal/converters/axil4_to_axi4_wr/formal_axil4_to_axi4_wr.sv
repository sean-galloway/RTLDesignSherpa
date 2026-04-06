// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axil4_to_axi4_wr -- pure combinational passthrough
// Verifies address/data passthrough, default field assignment, handshake forwarding

`include "reset_defs.svh"

module formal_axil4_to_axi4_wr #(
    parameter int AXI_ID_WIDTH   = 4,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1
) (
    input logic                        aclk,
    input logic                        aresetn,

    // Slave AXI4-Lite AW channel (free inputs)
    input logic [AXI_ADDR_WIDTH-1:0]   s_axil_awaddr,
    input logic [2:0]                  s_axil_awprot,
    input logic                        s_axil_awvalid,

    // Slave AXI4-Lite W channel (free inputs)
    input logic [AXI_DATA_WIDTH-1:0]   s_axil_wdata,
    input logic [AXI_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input logic                        s_axil_wvalid,

    // Slave AXI4-Lite B channel (free input)
    input logic                        s_axil_bready,

    // Master AXI4 AW channel (free input)
    input logic                        m_axi_awready,

    // Master AXI4 W channel (free input)
    input logic                        m_axi_wready,

    // Master AXI4 B channel (free inputs)
    input logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input logic [1:0]                  m_axi_bresp,
    input logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input logic                        m_axi_bvalid
);

    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8;
    localparam int SIZE_VAL   = $clog2(STRB_WIDTH);
    localparam int DEFAULT_ID = 0;

    // DUT outputs -- AW channel
    logic [AXI_ID_WIDTH-1:0]     m_axi_awid_o;
    logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr_o;
    logic [7:0]                  m_axi_awlen_o;
    logic [2:0]                  m_axi_awsize_o;
    logic [1:0]                  m_axi_awburst_o;
    logic                        m_axi_awlock_o;
    logic [3:0]                  m_axi_awcache_o;
    logic [2:0]                  m_axi_awprot_o;
    logic [3:0]                  m_axi_awqos_o;
    logic [3:0]                  m_axi_awregion_o;
    logic [AXI_USER_WIDTH-1:0]   m_axi_awuser_o;
    logic                        m_axi_awvalid_o;
    logic                        s_axil_awready_o;

    // DUT outputs -- W channel
    logic [AXI_DATA_WIDTH-1:0]   m_axi_wdata_o;
    logic [STRB_WIDTH-1:0]       m_axi_wstrb_o;
    logic                        m_axi_wlast_o;
    logic [AXI_USER_WIDTH-1:0]   m_axi_wuser_o;
    logic                        m_axi_wvalid_o;
    logic                        s_axil_wready_o;

    // DUT outputs -- B channel
    logic [1:0]                  s_axil_bresp_o;
    logic                        s_axil_bvalid_o;
    logic                        m_axi_bready_o;

    axil4_to_axi4_wr #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .DEFAULT_ID     (DEFAULT_ID),
        .DEFAULT_REGION (0),
        .DEFAULT_QOS    (0),
        .SKID_DEPTH_AW  (2),
        .SKID_DEPTH_W   (4),
        .SKID_DEPTH_B   (4)
    ) dut (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // Slave AXI4-Lite
        .s_axil_awaddr   (s_axil_awaddr),
        .s_axil_awprot   (s_axil_awprot),
        .s_axil_awvalid  (s_axil_awvalid),
        .s_axil_awready  (s_axil_awready_o),
        .s_axil_wdata    (s_axil_wdata),
        .s_axil_wstrb    (s_axil_wstrb),
        .s_axil_wvalid   (s_axil_wvalid),
        .s_axil_wready   (s_axil_wready_o),
        .s_axil_bresp    (s_axil_bresp_o),
        .s_axil_bvalid   (s_axil_bvalid_o),
        .s_axil_bready   (s_axil_bready),

        // Master AXI4
        .m_axi_awid      (m_axi_awid_o),
        .m_axi_awaddr    (m_axi_awaddr_o),
        .m_axi_awlen     (m_axi_awlen_o),
        .m_axi_awsize    (m_axi_awsize_o),
        .m_axi_awburst   (m_axi_awburst_o),
        .m_axi_awlock    (m_axi_awlock_o),
        .m_axi_awcache   (m_axi_awcache_o),
        .m_axi_awprot    (m_axi_awprot_o),
        .m_axi_awqos     (m_axi_awqos_o),
        .m_axi_awregion  (m_axi_awregion_o),
        .m_axi_awuser    (m_axi_awuser_o),
        .m_axi_awvalid   (m_axi_awvalid_o),
        .m_axi_awready   (m_axi_awready),
        .m_axi_wdata     (m_axi_wdata_o),
        .m_axi_wstrb     (m_axi_wstrb_o),
        .m_axi_wlast     (m_axi_wlast_o),
        .m_axi_wuser     (m_axi_wuser_o),
        .m_axi_wvalid    (m_axi_wvalid_o),
        .m_axi_wready    (m_axi_wready),
        .m_axi_bid       (m_axi_bid),
        .m_axi_bresp     (m_axi_bresp),
        .m_axi_buser     (m_axi_buser),
        .m_axi_bvalid    (m_axi_bvalid),
        .m_axi_bready    (m_axi_bready_o)
    );

    // =========================================================================
    // Past-valid counter
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // =========================================================================
    // AW Channel: Address passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_addr_passthrough: assert (m_axi_awaddr_o == s_axil_awaddr);
    end

    // =========================================================================
    // AW Channel: Prot passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_prot_passthrough: assert (m_axi_awprot_o == s_axil_awprot);
    end

    // =========================================================================
    // AW Channel: Valid passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_valid_passthrough: assert (m_axi_awvalid_o == s_axil_awvalid);
    end

    // =========================================================================
    // AW Channel: Ready passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_ready_passthrough: assert (s_axil_awready_o == m_axi_awready);
    end

    // =========================================================================
    // AW Channel: AWLEN always 0
    // =========================================================================
    always @(*) begin
        ap_awlen_zero: assert (m_axi_awlen_o == 8'd0);
    end

    // =========================================================================
    // AW Channel: AWBURST always INCR
    // =========================================================================
    always @(*) begin
        ap_awburst_incr: assert (m_axi_awburst_o == 2'b01);
    end

    // =========================================================================
    // AW Channel: AWID == DEFAULT_ID
    // =========================================================================
    always @(*) begin
        ap_awid_default: assert (m_axi_awid_o == AXI_ID_WIDTH'(DEFAULT_ID));
    end

    // =========================================================================
    // AW Channel: AWSIZE correct for data width
    // =========================================================================
    always @(*) begin
        ap_awsize_correct: assert (m_axi_awsize_o == 3'(SIZE_VAL));
    end

    // =========================================================================
    // AW Channel: AWLOCK always 0
    // =========================================================================
    always @(*) begin
        ap_awlock_zero: assert (m_axi_awlock_o == 1'b0);
    end

    // =========================================================================
    // AW Channel: AWCACHE always bufferable
    // =========================================================================
    always @(*) begin
        ap_awcache_default: assert (m_axi_awcache_o == 4'b0011);
    end

    // =========================================================================
    // AW Channel: AWUSER always 0
    // =========================================================================
    always @(*) begin
        ap_awuser_zero: assert (m_axi_awuser_o == '0);
    end

    // =========================================================================
    // W Channel: Data passthrough
    // =========================================================================
    always @(*) begin
        ap_w_data_passthrough: assert (m_axi_wdata_o == s_axil_wdata);
    end

    // =========================================================================
    // W Channel: Strobe passthrough
    // =========================================================================
    always @(*) begin
        ap_w_strb_passthrough: assert (m_axi_wstrb_o == s_axil_wstrb);
    end

    // =========================================================================
    // W Channel: Valid passthrough
    // =========================================================================
    always @(*) begin
        ap_w_valid_passthrough: assert (m_axi_wvalid_o == s_axil_wvalid);
    end

    // =========================================================================
    // W Channel: Ready passthrough
    // =========================================================================
    always @(*) begin
        ap_w_ready_passthrough: assert (s_axil_wready_o == m_axi_wready);
    end

    // =========================================================================
    // W Channel: WLAST always 1
    // =========================================================================
    always @(*) begin
        ap_wlast_one: assert (m_axi_wlast_o == 1'b1);
    end

    // =========================================================================
    // W Channel: WUSER always 0
    // =========================================================================
    always @(*) begin
        ap_wuser_zero: assert (m_axi_wuser_o == '0);
    end

    // =========================================================================
    // B Channel: Response passthrough
    // =========================================================================
    always @(*) begin
        ap_b_resp_passthrough: assert (s_axil_bresp_o == m_axi_bresp);
    end

    // =========================================================================
    // B Channel: Valid passthrough
    // =========================================================================
    always @(*) begin
        ap_b_valid_passthrough: assert (s_axil_bvalid_o == m_axi_bvalid);
    end

    // =========================================================================
    // B Channel: Ready passthrough
    // =========================================================================
    always @(*) begin
        ap_b_ready_passthrough: assert (m_axi_bready_o == s_axil_bready);
    end

    // =========================================================================
    // Cover: AW handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_aw_handshake: cover (s_axil_awvalid && s_axil_awready_o);
    end

    // =========================================================================
    // Cover: W handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_w_handshake: cover (s_axil_wvalid && s_axil_wready_o);
    end

    // =========================================================================
    // Cover: B handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_b_handshake: cover (s_axil_bvalid_o && s_axil_bready);
    end

endmodule
