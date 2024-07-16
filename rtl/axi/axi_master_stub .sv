`timescale 1ns / 1ps

module axi_master_stub
#(
    parameter int SKID_DEPTH_AW          = 2,
    parameter int SKID_DEPTH_W           = 4,
    parameter int SKID_DEPTH_B           = 2,
    parameter int SKID_DEPTH_AR          = 2,
    parameter int SKID_DEPTH_R           = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short and aclculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [AXI_DATA_WIDTH-1:0]  m_axi_wdata,
    output logic [AXI_WSTRB_WIDTH-1:0] m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Stub Outputs/Inputs
    // AW interface
    input  logic                       r_m_axi_awvalid,
    output logic                       r_m_axi_awready,
    output logic [2:0]                 r_m_axi_aw_count,
    input  logic [AWSize-1:0]          r_m_axi_aw_pkt,

    // W interface
    input  logic                       r_m_axi_wvalid,
    output logic                       r_m_axi_wready,
    input  logic [WSize-1:0]           r_m_axi_w_pkt,

    // B interface
    output logic                       r_m_axi_bvalid,
    input  logic                       r_m_axi_bready,
    output logic [BSize-1:0]           r_m_axi_b_pkt,

    // AR interface
    input  logic                       r_m_axi_arvalid,
    output logic                       r_m_axi_arready,
    input  logic [2:0]                 r_m_axi_ar_count,
    input  logic [ARSize-1:0]          r_m_axi_ar_pkt,

    // R interface
    output logic                       r_m_axi_rvalid,
    input  logic                       r_m_axi_rready,
    output logic [RSize-1:0]           r_m_axi_r_pkt
);

axi_master_wr_stub #(
    .SKID_DEPTH_AW       (SKID_DEPTH_AW),
    .SKID_DEPTH_W        (SKID_DEPTH_W),
    .SKID_DEPTH_B        (SKID_DEPTH_B),
    .AXI_ID_WIDTH        (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH      (AXI_USER_WIDTH),
    .AXI_WSTRB_WIDTH     (AXI_DATA_WIDTH/8),
    // Short and aclculated params
    .AW                  (AXI_ADDR_WIDTH),
    .DW                  (AXI_DATA_WIDTH),
    .IW                  (AXI_ID_WIDTH),
    .SW                  (AXI_WSTRB_WIDTH),
    .UW                  (AXI_USER_WIDTH),
    .AWSize              (IW+AW+8+3+2+1+4+3+4+4+UW),
    .WSize               (DW+SW+1+UW),
    .BSize               (IW+2+UW)
) u_axi_master_wr_stub (
    // Global Clock and Reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // Write address channel (AW)
    .m_axi_awid          (m_axi_awid),
    .m_axi_awaddr        (m_axi_awaddr),
    .m_axi_awlen         (m_axi_awlen),
    .m_axi_awsize        (m_axi_awsize),
    .m_axi_awburst       (m_axi_awburst),
    .m_axi_awlock        (m_axi_awlock),
    .m_axi_awcache       (m_axi_awcache),
    .m_axi_awprot        (m_axi_awprot),
    .m_axi_awqos         (m_axi_awqos),
    .m_axi_awregion      (m_axi_awregion),
    .m_axi_awuser        (m_axi_awuser),
    .m_axi_awvalid       (m_axi_awvalid),
    .m_axi_awready       (m_axi_awready),
    // Write data channel (W)
    .m_axi_wdata         (m_axi_wdata),
    .m_axi_wstrb         (m_axi_wstrb),
    .m_axi_wlast         (m_axi_wlast),
    .m_axi_wuser         (m_axi_wuser),
    .m_axi_wvalid        (m_axi_wvalid),
    .m_axi_wready        (m_axi_wready),
    // Write response channel (B)
    .m_axi_bid           (m_axi_bid),
    .m_axi_bresp         (m_axi_bresp),
    .m_axi_buser         (m_axi_buser),
    .m_axi_bvalid        (m_axi_bvalid),
    .m_axi_bready        (m_axi_bready),
    // Stub Outputs/Inputs
    // AW interface
    .r_m_axi_awvalid     (r_m_axi_awvalid),
    .r_m_axi_awready     (r_m_axi_awready),
    .r_m_axi_aw_count    (r_m_axi_aw_count),
    .r_m_axi_aw_pkt      (r_m_axi_aw_pkt),
    // W interface
    .r_m_axi_wvalid      (r_m_axi_wvalid),
    .r_m_axi_wready      (r_m_axi_wready),
    .r_m_axi_w_pkt       (r_m_axi_w_pkt),
    // B interface
    .r_m_axi_bvalid      (r_m_axi_bvalid),
    .r_m_axi_bready      (r_m_axi_bready),
    .r_m_axi_b_pkt       (r_m_axi_b_pkt)
);

axi_master_rd_stub #(
    .SKID_DEPTH_AR       (SKID_DEPTH_AR),
    .SKID_DEPTH_R        (SKID_DEPTH_R),
    .AXI_ID_WIDTH        (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH      (AXI_USER_WIDTH),
    .AXI_WSTRB_WIDTH     (AXI_DATA_WIDTH/8),
    // Short and aclculated params
    .AW                  (AXI_ADDR_WIDTH),
    .DW                  (AXI_DATA_WIDTH),
    .IW                  (AXI_ID_WIDTH),
    .SW                  (AXI_WSTRB_WIDTH),
    .UW                  (AXI_USER_WIDTH),
    .ARSize              (IW+AW+8+3+2+1+4+3+4+4+UW),
    .RSize               (IW+DW+2+1+UW)
) u_axi_master_rd_stub (
    // Global Clock and Reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // Read address channel (AR)
    .m_axi_arid          (m_axi_arid),
    .m_axi_araddr        (m_axi_araddr),
    .m_axi_arlen         (m_axi_arlen),
    .m_axi_arsize        (m_axi_arsize),
    .m_axi_arburst       (m_axi_arburst),
    .m_axi_arlock        (m_axi_arlock),
    .m_axi_arcache       (m_axi_arcache),
    .m_axi_arprot        (m_axi_arprot),
    .m_axi_arqos         (m_axi_arqos),
    .m_axi_arregion      (m_axi_arregion),
    .m_axi_aruser        (m_axi_aruser),
    .m_axi_arvalid       (m_axi_arvalid),
    .m_axi_arready       (m_axi_arready),
    // Read data channel (R)
    .m_axi_rid           (m_axi_rid),
    .m_axi_rdata         (m_axi_rdata),
    .m_axi_rresp         (m_axi_rresp),
    .m_axi_rlast         (m_axi_rlast),
    .m_axi_ruser         (m_axi_ruser),
    .m_axi_rvalid        (m_axi_rvalid),
    .m_axi_rready        (m_axi_rready),
    // Stub Outputs/Inputs
    // AR interface
    .r_m_axi_arvalid     (r_m_axi_arvalid),
    .r_m_axi_arready     (r_m_axi_arready),
    .r_m_axi_ar_count    (r_m_axi_ar_count),
    .r_m_axi_ar_pkt      (r_m_axi_ar_pkt),
    // R interface
    .r_m_axi_rvalid      (r_m_axi_rvalid),
    .r_m_axi_rready      (r_m_axi_rready),
    .r_m_axi_r_pkt       (r_m_axi_r_pkt)
);

endmodule : axi_master_stub
