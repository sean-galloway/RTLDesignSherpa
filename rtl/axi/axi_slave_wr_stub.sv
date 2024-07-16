`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi_slave_wr_stub
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
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
    input  logic [BSize-1:0]           r_s_axi_b_pkt

);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_AW), .DATA_WIDTH(AWSize)) inst_aw_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_awvalid),
        .o_wr_ready               (s_axi_awready),
        .i_wr_data                ({s_axi_awid,s_axi_awaddr,s_axi_awlen,s_axi_awsize,s_axi_awburst,
                                    s_axi_awlock,s_axi_awcache,s_axi_awprot,s_axi_awqos,
                                    s_axi_awregion,s_axi_awuser}),
        .o_rd_valid               (r_s_axi_awvalid),
        .i_rd_ready               (r_s_axi_awready),
        .o_rd_count               (r_s_axi_aw_count),
        .o_rd_data                (r_s_axi_aw_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_W), .DATA_WIDTH(WSize)) inst_w_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_wvalid),
        .o_wr_ready               (s_axi_wready),
        .i_wr_data                ({s_axi_wdata,s_axi_wstrb,s_axi_wlast,s_axi_wuser}),
        .o_rd_valid               (r_s_axi_wvalid),
        .i_rd_ready               (r_s_axi_wready),
        .o_rd_data                (r_s_axi_w_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_B), .DATA_WIDTH(BSize)) inst_b_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_s_axi_bvalid),
        .o_wr_ready               (r_s_axi_bready),
        .i_wr_data                (r_s_axi_b_pkt),
        .o_rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .o_rd_data                ({s_axi_bid,s_axi_bresp,s_axi_buser})
    );

endmodule : axi_slave_wr_stub
