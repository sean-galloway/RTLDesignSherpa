`timescale 1ns / 1ps
`include "axi_params.svh"

// Generic Slave module to prove out maximal performance
module axi_slave
// #(
//     parameter int AXI_ID_WIDTH      = 4,
//     parameter int AXI_ADDR_WIDTH    = 32,
//     parameter int AXI_DATA_WIDTH    = 32,
//     parameter int AXI_USER_WIDTH    = 1,
//     parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8
// )
(
    // Global Clock and Reset
    input  logic s_axi_aclk,
    input  logic s_axi_aresetn,

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
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_wid,
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

    // Write Fifo Channel, out
    output  logic                      o_wr_pkt_valid,
    input   logic                      i_wr_pkt_ready,
    output  logic [WrPkt-1:0]          o_wr_pkt_data,

    // Read Fifo Channel, out
    output  logic                      o_rd_pkt_valid,
    input   logic                      i_rd_pkt_ready,
    output  logic [RdPkt-1:0]          o_rd_pkt_data,

    // Read Fifo Channel, ret
    input   logic                      i_rdret_pkt_valid,
    output  logic                      o_rdret_pkt_ready,
    input   logic [DW-1:0]             i_rdret_pkt_data
);

    localparam int AW       = AXI_ADDR_WIDTH;
    localparam int DW       = AXI_DATA_WIDTH;
    localparam int IW       = AXI_DATA_WIDTH;
    localparam int WrPkt    = AW+DW+AXI_WSTRB_WIDTH;
    localparam int RdPkt    = AW;



endmodule : axi_slave
