`timescale 1ns / 1ps

module axi_wr_noscale
#(
    parameter int SKID_DEPTH_AW          = 2,
    parameter int SKID_DEPTH_W           = 4,
    parameter int SKID_DEPTH_B           = 2,
    parameter int SKID_DEPTH_AR          = 2,
    parameter int SKID_DEPTH_R           = 4,

    parameter int AXI_ID_WIDTH        = 8,
    parameter int AXI_ADDR_WIDTH      = 32,
    parameter int AXI_MST_DATA_WIDTH  = 32,
    parameter int AXI_SLV_DATA_WIDTH  = 32,
    parameter int AXI_USER_WIDTH      = 1,
    parameter int AXI_MST_WSTRB_WIDTH = AXI_MST_DATA_WIDTH / 8,
    parameter int AXI_SLV_WSTRB_WIDTH = AXI_SLV_DATA_WIDTH / 8,
    // Short and aclculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int MDW      = AXI_MST_DATA_WIDTH,
    parameter int SDW      = AXI_SLV_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int MSW      = AXI_MST_WSTRB_WIDTH,
    parameter int SSW      = AXI_SLV_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int MAWSize  = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int MWSize   = MDW+MSW+1+UW,
    parameter int SAWSize  = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int SWSize   = SDW+SSW+1+UW,
    parameter int BSize    = IW+2+UW
) (
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]        s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]      s_axi_awaddr,
    input  logic [7:0]                     s_axi_awlen,
    input  logic [2:0]                     s_axi_awsize,
    input  logic [1:0]                     s_axi_awburst,
    input  logic                           s_axi_awlock,
    input  logic [3:0]                     s_axi_awcache,
    input  logic [2:0]                     s_axi_awprot,
    input  logic [3:0]                     s_axi_awqos,
    input  logic [3:0]                     s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_awuser,
    input  logic                           s_axi_awvalid,
    output logic                           s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_MST_DATA_WIDTH-1:0]  s_axi_wdata,
    input  logic [AXI_MST_WSTRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                           s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_wuser,
    input  logic                           s_axi_wvalid,
    output logic                           s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]        s_axi_bid,
    output logic [1:0]                     s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]      s_axi_buser,
    output logic                           s_axi_bvalid,
    input  logic                           s_axi_bready,

    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]        m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]      m_axi_awaddr,
    output logic [7:0]                     m_axi_awlen,
    output logic [2:0]                     m_axi_awsize,
    output logic [1:0]                     m_axi_awburst,
    output logic                           m_axi_awlock,
    output logic [3:0]                     m_axi_awcache,
    output logic [2:0]                     m_axi_awprot,
    output logic [3:0]                     m_axi_awqos,
    output logic [3:0]                     m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]      m_axi_awuser,
    output logic                           m_axi_awvalid,
    input  logic                           m_axi_awready,

    // Write data channel (W)
    output logic [AXI_MST_DATA_WIDTH-1:0]  m_axi_wdata,
    output logic [AXI_MST_WSTRB_WIDTH-1:0] m_axi_wstrb,
    output logic                           m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]      m_axi_wuser,
    output logic                           m_axi_wvalid,
    input  logic                           m_axi_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]        m_axi_bid,
    input  logic [1:0]                     m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]      m_axi_buser,
    input  logic                           m_axi_bvalid,
    output logic                           m_axi_bready
);

    logic                       r_s_axi_awvalid;
    logic                       r_s_axi_awready;
    logic [3:0]                 r_s_axi_aw_count;
    logic [SAWSize-1:0]         r_s_axi_aw_pkt;

    // W interface
    logic                       r_s_axi_wvalid;
    logic                       r_s_axi_wready;
    logic [SWSize-1:0]          r_s_axi_w_pkt;

    // B interface
    logic                       r_s_axi_bvalid;
    logic                       r_s_axi_bready;
    logic [BSize-1:0]           r_s_axi_b_pkt;

    // AW interface
    logic                       r_m_axi_awvalid;
    logic                       r_m_axi_awready;
    logic [3:0]                 r_m_axi_aw_count;
    logic [MAWSize-1:0]         r_m_axi_aw_pkt;

    // W interface
    logic                       r_m_axi_wvalid;
    logic                       r_m_axi_wready;
    logic [MWSize-1:0]          r_m_axi_w_pkt;

    // B interface
    logic                       r_m_axi_bvalid;
    logic                       r_m_axi_bready;
    logic [BSize-1:0]           r_m_axi_b_pkt;

    // AW Interface
    assign r_m_axi_awvalid = r_s_axi_awvalid;
    assign r_s_axi_awready = r_m_axi_awready;
    assign r_m_axi_aw_pkt  = r_s_axi_aw_pkt;
    // W Interface
    assign r_m_axi_wvalid = r_s_axi_wvalid;
    assign r_s_axi_wready = r_m_axi_wready;
    assign r_m_axi_w_pkt  = r_s_axi_w_pkt;
    // B Interface
    assign r_s_axi_bvalid = r_m_axi_bvalid;
    assign r_m_axi_bready = r_s_axi_bready;
    assign r_s_axi_b_pkt  = r_m_axi_b_pkt;

    axi_slave_wr_stub #(
        .SKID_DEPTH_AW          (SKID_DEPTH_AW),
        .SKID_DEPTH_W           (SKID_DEPTH_W),
        .SKID_DEPTH_B           (SKID_DEPTH_B),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH         (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH         (AXI_SLV_DATA_WIDTH),
        .AXI_USER_WIDTH         (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH        (AXI_SLV_WSTRB_WIDTH)
    ) axi_slave_wr_stub_inst (
        .aclk                   (aclk),
        .aresetn                (aresetn),
        // Write address channel (AW)
        .s_axi_awid             (s_axi_awid),
        .s_axi_awaddr           (s_axi_awaddr),
        .s_axi_awlen            (s_axi_awlen),
        .s_axi_awsize           (s_axi_awsize),
        .s_axi_awburst          (s_axi_awburst),
        .s_axi_awlock           (s_axi_awlock),
        .s_axi_awcache          (s_axi_awcache),
        .s_axi_awprot           (s_axi_awprot),
        .s_axi_awqos            (s_axi_awqos),
        .s_axi_awregion         (s_axi_awregion),
        .s_axi_awuser           (s_axi_awuser),
        .s_axi_awvalid          (s_axi_awvalid),
        .s_axi_awready          (s_axi_awready),
        // Write data channel (W)
        .s_axi_wdata            (s_axi_wdata),
        .s_axi_wstrb            (s_axi_wstrb),
        .s_axi_wlast            (s_axi_wlast),
        .s_axi_wuser            (s_axi_wuser),
        .s_axi_wvalid           (s_axi_wvalid),
        .s_axi_wready           (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid              (s_axi_bid),
        .s_axi_bresp            (s_axi_bresp),
        .s_axi_buser            (s_axi_buser),
        .s_axi_bvalid           (s_axi_bvalid),
        .s_axi_bready           (s_axi_bready),
        // Stub Outputs/Inputs
        // AW interface
        .r_s_axi_awvalid        (r_s_axi_awvalid),
        .r_s_axi_awready        (r_s_axi_awready),
        .r_s_axi_aw_count       (r_s_axi_aw_count),
        .r_s_axi_aw_pkt         (r_s_axi_aw_pkt),
        // W interface
        .r_s_axi_wvalid         (r_s_axi_wvalid),
        .r_s_axi_wready         (r_s_axi_wready),
        .r_s_axi_w_pkt          (r_s_axi_w_pkt),
        // B interface
        .r_s_axi_bvalid         (r_s_axi_bvalid),
        .r_s_axi_bready         (r_s_axi_bready),
        .r_s_axi_b_pkt          (r_s_axi_b_pkt)
    );

    axi_master_wr_stub #(
        .SKID_DEPTH_AW       (SKID_DEPTH_AW),
        .SKID_DEPTH_W        (SKID_DEPTH_W),
        .SKID_DEPTH_B        (SKID_DEPTH_B),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_MST_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH     (AXI_MST_WSTRB_WIDTH)
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

endmodule : axi_wr_noscale
