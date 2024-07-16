`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi_slave_stub
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short params and calculations
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
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]  s_axi_wdata,
    input  logic [AXI_WSTRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Stub Outputs/Inputs
    // AW interface
    output logic                       r_s_axi_awvalid,
    input  logic                       r_s_axi_awready,
    output logic [2:0]                 r_s_axi_aw_count,
    output logic [AWSize-1:0]          r_s_axi_aw_pkt,

    // W interface
    output logic                       r_s_axi_wvalid,
    input  logic                       r_s_axi_wready,
    output logic [WSize-1:0]           r_s_axi_w_pkt,

    // B interface
    input  logic                       r_s_axi_bvalid,
    output logic                       r_s_axi_bready,
    input  logic [BSize-1:0]           r_s_axi_b_pkt,

    // AR interface
    output logic                       r_s_axi_arvalid,
    input  logic                       r_s_axi_arready,
    output logic [2:0]                 r_s_axi_ar_count,
    output logic [ARSize-1:0]          r_s_axi_ar_pkt,

    // R interface
    input  logic                       r_s_axi_rvalid,
    output logic                       r_s_axi_rready,
    input  logic [RSize-1:0]           r_s_axi_r_pkt
);

axi_slave_wr_stub #(
    .SKID_DEPTH_AW       (SKID_DEPTH_AW),
    .SKID_DEPTH_W        (SKID_DEPTH_W),
    .SKID_DEPTH_B        (SKID_DEPTH_B),
    .AXI_ID_WIDTH        (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH      (AXI_USER_WIDTH),
    .AXI_WSTRB_WIDTH     (AXI_DATA_WIDTH/8),
    // Short params and calculations
    .AW                  (AXI_ADDR_WIDTH),
    .DW                  (AXI_DATA_WIDTH),
    .IW                  (AXI_ID_WIDTH),
    .SW                  (AXI_WSTRB_WIDTH),
    .UW                  (AXI_USER_WIDTH),
    .AWSize              (IW+AW+8+3+2+1+4+3+4+4+UW),
    .WSize               (DW+SW+1+UW),
    .BSize               (IW+2+UW)
) u_axi_slave_wr_stub (
    // Global Clock and Reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // Write address channel (AW)
    .s_axi_awid          (s_axi_awid),
    .s_axi_awaddr        (s_axi_awaddr),
    .s_axi_awlen         (s_axi_awlen),
    .s_axi_awsize        (s_axi_awsize),
    .s_axi_awburst       (s_axi_awburst),
    .s_axi_awlock        (s_axi_awlock),
    .s_axi_awcache       (s_axi_awcache),
    .s_axi_awprot        (s_axi_awprot),
    .s_axi_awqos         (s_axi_awqos),
    .s_axi_awregion      (s_axi_awregion),
    .s_axi_awuser        (s_axi_awuser),
    .s_axi_awvalid       (s_axi_awvalid),
    .s_axi_awready       (s_axi_awready),
    // Write data channel (W)
    .s_axi_wdata         (s_axi_wdata),
    .s_axi_wstrb         (s_axi_wstrb),
    .s_axi_wlast         (s_axi_wlast),
    .s_axi_wuser         (s_axi_wuser),
    .s_axi_wvalid        (s_axi_wvalid),
    .s_axi_wready        (s_axi_wready),
    // Write response channel (B)
    .s_axi_bid           (s_axi_bid),
    .s_axi_bresp         (s_axi_bresp),
    .s_axi_buser         (s_axi_buser),
    .s_axi_bvalid        (s_axi_bvalid),
    .s_axi_bready        (s_axi_bready),
    // Stub Outputs/Inputs
    // AW interface
    .r_s_axi_awvalid     (r_s_axi_awvalid),
    .r_s_axi_awready     (r_s_axi_awready),
    .r_s_axi_aw_count    (r_s_axi_aw_count),
    .r_s_axi_aw_pkt      (r_s_axi_aw_pkt),
    // W interface
    .r_s_axi_wvalid      (r_s_axi_wvalid),
    .r_s_axi_wready      (r_s_axi_wready),
    .r_s_axi_w_pkt       (r_s_axi_w_pkt),
    // B interface
    .r_s_axi_bvalid      (r_s_axi_bvalid),
    .r_s_axi_bready      (r_s_axi_bready),
    .r_s_axi_b_pkt       (r_s_axi_b_pkt)
);

axi_slave_rd_stub #(
    .SKID_DEPTH_AR       (SKID_DEPTH_AR),
    .SKID_DEPTH_R        (SKID_DEPTH_R),
    .AXI_ID_WIDTH        (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH      (AXI_USER_WIDTH),
    .AXI_WSTRB_WIDTH     (AXI_DATA_WIDTH/8),
    // Short params and calculations
    .AW                  (AXI_ADDR_WIDTH),
    .DW                  (AXI_DATA_WIDTH),
    .IW                  (AXI_ID_WIDTH),
    .SW                  (AXI_WSTRB_WIDTH),
    .UW                  (AXI_USER_WIDTH),
    .ARSize              (IW+AW+8+3+2+1+4+3+4+4+UW),
    .RSize               (IW+DW+2+1+UW)
) u_axi_slave_rd_stub (
    // Global Clock and Reset
    .aclk                (aclk),
    .aresetn             (aresetn),
    // Read address channel (AR)
    .s_axi_arid          (s_axi_arid),
    .s_axi_araddr        (s_axi_araddr),
    .s_axi_arlen         (s_axi_arlen),
    .s_axi_arsize        (s_axi_arsize),
    .s_axi_arburst       (s_axi_arburst),
    .s_axi_arlock        (s_axi_arlock),
    .s_axi_arcache       (s_axi_arcache),
    .s_axi_arprot        (s_axi_arprot),
    .s_axi_arqos         (s_axi_arqos),
    .s_axi_arregion      (s_axi_arregion),
    .s_axi_aruser        (s_axi_aruser),
    .s_axi_arvalid       (s_axi_arvalid),
    .s_axi_arready       (s_axi_arready),
    // Read data channel (R)
    .s_axi_rid           (s_axi_rid),
    .s_axi_rdata         (s_axi_rdata),
    .s_axi_rresp         (s_axi_rresp),
    .s_axi_rlast         (s_axi_rlast),
    .s_axi_ruser         (s_axi_ruser),
    .s_axi_rvalid        (s_axi_rvalid),
    .s_axi_rready        (s_axi_rready),
    // Stub Outputs/Inputs
    // AR interface
    .r_s_axi_arvalid     (r_s_axi_arvalid),
    .r_s_axi_arready     (r_s_axi_arready),
    .r_s_axi_ar_count    (r_s_axi_ar_count),
    .r_s_axi_ar_pkt      (r_s_axi_ar_pkt),
    // R interface
    .r_s_axi_rvalid      (r_s_axi_rvalid),
    .r_s_axi_rready      (r_s_axi_rready),
    .r_s_axi_r_pkt       (r_s_axi_r_pkt)
);


endmodule : axi_slave_stub
