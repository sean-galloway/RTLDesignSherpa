`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi_slave_wr_stub
#(
    parameter int DEPTH_AW          = 2,
    parameter int DEPTH_W           = 4,
    parameter int DEPTH_B           = 2,
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
    parameter int BSize    = IW+2+UW
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

    // Stub Outputs/Inputs
    // AW interface
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,
    output logic [3:0]                 fub_axi_aw_count,
    output logic [AWSize-1:0]          fub_axi_aw_pkt,

    // W interface
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,
    output logic [WSize-1:0]           fub_axi_w_pkt,

    // B interface
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,
    input  logic [BSize-1:0]           fub_axi_b_pkt

);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    gaxi_skid_buffer #(.DEPTH(DEPTH_AW), .DATA_WIDTH(AWSize)) inst_aw_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_awvalid),
        .wr_ready               (s_axi_awready),
        .i_wr_data                ({s_axi_awid,s_axi_awaddr,s_axi_awlen,s_axi_awsize,s_axi_awburst,
                                    s_axi_awlock,s_axi_awcache,s_axi_awprot,s_axi_awqos,
                                    s_axi_awregion,s_axi_awuser}),
        .rd_valid               (fub_axi_awvalid),
        .i_rd_ready               (fub_axi_awready),
        .rd_count               (fub_axi_aw_count),
        .rd_data                (fub_axi_aw_pkt),
        .count                 ()
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    gaxi_skid_buffer #(.DEPTH(DEPTH_W), .DATA_WIDTH(WSize)) inst_w_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_wvalid),
        .wr_ready               (s_axi_wready),
        .i_wr_data                ({s_axi_wdata,s_axi_wstrb,s_axi_wlast,s_axi_wuser}),
        .rd_valid               (fub_axi_wvalid),
        .i_rd_ready               (fub_axi_wready),
        .rd_data                (fub_axi_w_pkt),
        .rd_count               (),
        .count                 ()
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    gaxi_skid_buffer #(.DEPTH(DEPTH_B), .DATA_WIDTH(BSize)) inst_b_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_axi_bvalid),
        .wr_ready               (fub_axi_bready),
        .i_wr_data                (fub_axi_b_pkt),
        .rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .rd_data                ({s_axi_bid,s_axi_bresp,s_axi_buser}),
        .rd_count               (),
        .count                 ()
    );

endmodule : axi_slave_wr_stub
