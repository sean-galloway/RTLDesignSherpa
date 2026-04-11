// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axil4_to_axi4 -- combined rd+wr wrapper
// Verifies signal passthrough, default field assignment, no cross-contamination
// between read and write paths. The actual conversion logic is proved in
// axil4_to_axi4_rd and _wr proofs; this proof ensures the wrapper wiring.

`include "reset_defs.svh"

module formal_axil4_to_axi4 #(
    parameter int AXI_ID_WIDTH   = 2,
    parameter int AXI_ADDR_WIDTH = 16,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int DEFAULT_ID     = 0,
    parameter int DEFAULT_REGION = 0,
    parameter int DEFAULT_QOS    = 0,
    parameter int SKID_DEPTH_AR  = 2,
    parameter int SKID_DEPTH_AW  = 2,
    parameter int SKID_DEPTH_W   = 2,
    parameter int SKID_DEPTH_R   = 2,
    parameter int SKID_DEPTH_B   = 2
) (
    input logic aclk,
    input logic aresetn
);

    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8;
    localparam int SIZE_VAL   = $clog2(STRB_WIDTH);

    // =========================================================================
    // Free inputs -- slave AXI4-Lite side
    // =========================================================================

    // Read Address Channel
    logic [AXI_ADDR_WIDTH-1:0]                 s_axil_araddr;
    logic [2:0]                                s_axil_arprot;
    logic                                      s_axil_arvalid;

    // Read Data Channel
    logic                                      s_axil_rready;

    // Write Address Channel
    logic [AXI_ADDR_WIDTH-1:0]                 s_axil_awaddr;
    logic [2:0]                                s_axil_awprot;
    logic                                      s_axil_awvalid;

    // Write Data Channel
    logic [AXI_DATA_WIDTH-1:0]                 s_axil_wdata;
    logic [STRB_WIDTH-1:0]                     s_axil_wstrb;
    logic                                      s_axil_wvalid;

    // Write Response Channel
    logic                                      s_axil_bready;

    // =========================================================================
    // Free inputs -- master AXI4 side
    // =========================================================================

    // Read
    logic                                      m_axi_arready;
    logic [AXI_ID_WIDTH-1:0]                   m_axi_rid;
    logic [AXI_DATA_WIDTH-1:0]                 m_axi_rdata;
    logic [1:0]                                m_axi_rresp;
    logic                                      m_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]                 m_axi_ruser;
    logic                                      m_axi_rvalid;

    // Write
    logic                                      m_axi_awready;
    logic                                      m_axi_wready;
    logic [AXI_ID_WIDTH-1:0]                   m_axi_bid;
    logic [1:0]                                m_axi_bresp;
    logic [AXI_USER_WIDTH-1:0]                 m_axi_buser;
    logic                                      m_axi_bvalid;

    // =========================================================================
    // DUT outputs
    // =========================================================================

    // Slave side outputs
    logic                        s_axil_arready_o;
    logic [AXI_DATA_WIDTH-1:0]   s_axil_rdata_o;
    logic [1:0]                  s_axil_rresp_o;
    logic                        s_axil_rvalid_o;

    logic                        s_axil_awready_o;
    logic                        s_axil_wready_o;
    logic [1:0]                  s_axil_bresp_o;
    logic                        s_axil_bvalid_o;

    // Master side outputs
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
    logic [AXI_DATA_WIDTH-1:0]   m_axi_wdata_o;
    logic [STRB_WIDTH-1:0]       m_axi_wstrb_o;
    logic                        m_axi_wlast_o;
    logic [AXI_USER_WIDTH-1:0]   m_axi_wuser_o;
    logic                        m_axi_wvalid_o;
    logic                        m_axi_bready_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================

    axil4_to_axi4 #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .DEFAULT_ID     (DEFAULT_ID),
        .DEFAULT_REGION (DEFAULT_REGION),
        .DEFAULT_QOS    (DEFAULT_QOS),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_AW  (SKID_DEPTH_AW),
        .SKID_DEPTH_W   (SKID_DEPTH_W),
        .SKID_DEPTH_R   (SKID_DEPTH_R),
        .SKID_DEPTH_B   (SKID_DEPTH_B)
    ) dut (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // Slave AXI4-Lite Read
        .s_axil_araddr   (s_axil_araddr),
        .s_axil_arprot   (s_axil_arprot),
        .s_axil_arvalid  (s_axil_arvalid),
        .s_axil_arready  (s_axil_arready_o),
        .s_axil_rdata    (s_axil_rdata_o),
        .s_axil_rresp    (s_axil_rresp_o),
        .s_axil_rvalid   (s_axil_rvalid_o),
        .s_axil_rready   (s_axil_rready),

        // Slave AXI4-Lite Write
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

        // Master AXI4 Read
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
        .m_axi_rready    (m_axi_rready_o),

        // Master AXI4 Write
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
    // P1: AR address passthrough (Lite addr -> AXI4 addr)
    // =========================================================================
    always @(*) begin
        ap_ar_addr_passthrough: assert (m_axi_araddr_o == s_axil_araddr);
    end

    // =========================================================================
    // P2: AR prot passthrough
    // =========================================================================
    always @(*) begin
        ap_ar_prot_passthrough: assert (m_axi_arprot_o == s_axil_arprot);
    end

    // =========================================================================
    // P3: AR valid passthrough
    // =========================================================================
    always @(*) begin
        ap_ar_valid_passthrough: assert (m_axi_arvalid_o == s_axil_arvalid);
    end

    // =========================================================================
    // P4: AR ready passthrough
    // =========================================================================
    always @(*) begin
        ap_ar_ready_passthrough: assert (s_axil_arready_o == m_axi_arready);
    end

    // =========================================================================
    // P5: ARLEN always 0 (single beat)
    // =========================================================================
    always @(*) begin
        ap_arlen_zero: assert (m_axi_arlen_o == 8'd0);
    end

    // =========================================================================
    // P6: ARBURST always INCR
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
    // P9: AW address passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_addr_passthrough: assert (m_axi_awaddr_o == s_axil_awaddr);
    end

    // =========================================================================
    // P10: AW prot passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_prot_passthrough: assert (m_axi_awprot_o == s_axil_awprot);
    end

    // =========================================================================
    // P11: AW valid passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_valid_passthrough: assert (m_axi_awvalid_o == s_axil_awvalid);
    end

    // =========================================================================
    // P12: AW ready passthrough
    // =========================================================================
    always @(*) begin
        ap_aw_ready_passthrough: assert (s_axil_awready_o == m_axi_awready);
    end

    // =========================================================================
    // P13: AWLEN always 0
    // =========================================================================
    always @(*) begin
        ap_awlen_zero: assert (m_axi_awlen_o == 8'd0);
    end

    // =========================================================================
    // P14: AWBURST always INCR
    // =========================================================================
    always @(*) begin
        ap_awburst_incr: assert (m_axi_awburst_o == 2'b01);
    end

    // =========================================================================
    // P15: AWID == DEFAULT_ID
    // =========================================================================
    always @(*) begin
        ap_awid_default: assert (m_axi_awid_o == AXI_ID_WIDTH'(DEFAULT_ID));
    end

    // =========================================================================
    // P16: AWSIZE correct for data width
    // =========================================================================
    always @(*) begin
        ap_awsize_correct: assert (m_axi_awsize_o == 3'(SIZE_VAL));
    end

    // =========================================================================
    // P17: W data passthrough
    // =========================================================================
    always @(*) begin
        ap_wdata_passthrough: assert (m_axi_wdata_o == s_axil_wdata);
    end

    // =========================================================================
    // P18: W strobe passthrough
    // =========================================================================
    always @(*) begin
        ap_wstrb_passthrough: assert (m_axi_wstrb_o == s_axil_wstrb);
    end

    // =========================================================================
    // P19: W valid passthrough
    // =========================================================================
    always @(*) begin
        ap_wvalid_passthrough: assert (m_axi_wvalid_o == s_axil_wvalid);
    end

    // =========================================================================
    // P20: WLAST always 1 (single beat)
    // =========================================================================
    always @(*) begin
        ap_wlast_always_one: assert (m_axi_wlast_o == 1'b1);
    end

    // =========================================================================
    // P21: R data passthrough
    // =========================================================================
    always @(*) begin
        ap_rdata_passthrough: assert (s_axil_rdata_o == m_axi_rdata);
    end

    // =========================================================================
    // P22: R resp passthrough
    // =========================================================================
    always @(*) begin
        ap_rresp_passthrough: assert (s_axil_rresp_o == m_axi_rresp);
    end

    // =========================================================================
    // P23: R valid passthrough
    // =========================================================================
    always @(*) begin
        ap_rvalid_passthrough: assert (s_axil_rvalid_o == m_axi_rvalid);
    end

    // =========================================================================
    // P24: R ready passthrough
    // =========================================================================
    always @(*) begin
        ap_rready_passthrough: assert (m_axi_rready_o == s_axil_rready);
    end

    // =========================================================================
    // P25: B resp passthrough
    // =========================================================================
    always @(*) begin
        ap_bresp_passthrough: assert (s_axil_bresp_o == m_axi_bresp);
    end

    // =========================================================================
    // P26: B valid passthrough
    // =========================================================================
    always @(*) begin
        ap_bvalid_passthrough: assert (s_axil_bvalid_o == m_axi_bvalid);
    end

    // =========================================================================
    // P27: B ready passthrough
    // =========================================================================
    always @(*) begin
        ap_bready_passthrough: assert (m_axi_bready_o == s_axil_bready);
    end

    // =========================================================================
    // P28: ARLOCK always 0
    // =========================================================================
    always @(*) begin
        ap_arlock_zero: assert (m_axi_arlock_o == 1'b0);
    end

    // =========================================================================
    // P29: AWLOCK always 0
    // =========================================================================
    always @(*) begin
        ap_awlock_zero: assert (m_axi_awlock_o == 1'b0);
    end

    // =========================================================================
    // P30: ARCACHE default (bufferable 4'b0011)
    // =========================================================================
    always @(*) begin
        ap_arcache_default: assert (m_axi_arcache_o == 4'b0011);
    end

    // =========================================================================
    // P31: AWCACHE default (bufferable 4'b0011)
    // =========================================================================
    always @(*) begin
        ap_awcache_default: assert (m_axi_awcache_o == 4'b0011);
    end

    // =========================================================================
    // Cover: AR handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_ar_handshake: cover (s_axil_arvalid && s_axil_arready_o);
    end

    // =========================================================================
    // Cover: AW handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_aw_handshake: cover (s_axil_awvalid && s_axil_awready_o);
    end

    // =========================================================================
    // Cover: R handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_r_handshake: cover (s_axil_rvalid_o && s_axil_rready);
    end

    // =========================================================================
    // Cover: B handshake
    // =========================================================================
    always @(posedge aclk) begin
        cp_b_handshake: cover (s_axil_bvalid_o && s_axil_bready);
    end

    // =========================================================================
    // Cover: Simultaneous read and write requests
    // =========================================================================
    always @(posedge aclk) begin
        cp_simultaneous_rd_wr: cover (
            s_axil_arvalid && s_axil_awvalid && s_axil_wvalid
        );
    end

endmodule
