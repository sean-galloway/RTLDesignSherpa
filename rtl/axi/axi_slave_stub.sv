`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi_slave_stub
#(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8
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
    output  logic                      r_s_axi_awvalid,
    input   logic                      r_s_axi_awready,
    output  logic [1:0]                r_s_axi_aw_count,
    output  logic [AWSize-1:0]         r_s_axi_aw_pkt,

    // W interface
    output  logic                      r_s_axi_wvalid,
    input   logic                      r_s_axi_wready,
    output  logic [WSize-1:0]          r_s_axi_w_pkt,

    // B interface
    input   logic                      r_s_axi_bvalid,
    output  logic                      r_s_axi_bready,
    input   logic [BSize-1:0]          r_s_axi_b_pkt,

    // AR interface
    output  logic                      r_s_axi_arvalid,
    input   logic                      r_s_axi_arready,
    output  logic [1:0]                r_s_axi_ar_count,
    output  logic [ARSize-1:0]         r_s_axi_ar_pkt,

    // R interface
    input   logic                      r_s_axi_rvalid,
    output  logic                      r_s_axi_rready,
    input   logic [RSize-1:0]          r_s_axi_r_pkt
);

    localparam int AW       = AXI_ADDR_WIDTH;
    localparam int DW       = AXI_DATA_WIDTH;
    localparam int IW       = AXI_ID_WIDTH;
    localparam int SW       = AXI_WSTRB_WIDTH;
    localparam int UW       = AXI_USER_WIDTH;
    localparam int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int WSize    = DW+SW+1+UW;
    localparam int BSize    = IW+2+UW;
    localparam int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW;
    localparam int RSize    = IW+DW+2+1+UW;

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    axi_skid_buffer #(.DATA_WIDTH(AWSize)) inst_aw_phase (
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
    axi_skid_buffer #(.DATA_WIDTH(WSize)) inst_w_phase (
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
    axi_skid_buffer #(.DATA_WIDTH(BSize)) inst_b_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_s_axi_bvalid),
        .o_wr_ready               (r_s_axi_bready),
        .i_wr_data                (r_s_axi_b_pkt),
        .o_rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .o_rd_data                ({s_axi_bid,s_axi_bresp,s_axi_buser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    axi_skid_buffer #(.DATA_WIDTH(ARSize)) inst_ar_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_arvalid),
        .o_wr_ready               (s_axi_arready),
        .i_wr_data                ({s_axi_arid,s_axi_araddr,s_axi_arlen,s_axi_arsize,s_axi_arburst,
                                    s_axi_arlock,s_axi_arcache,s_axi_arprot,s_axi_arqos,
                                    s_axi_arregion,s_axi_aruser}),
        .o_rd_valid               (r_s_axi_arvalid),
        .i_rd_ready               (r_s_axi_arready),
        .o_rd_count               (r_s_axi_ar_count),
        .o_rd_data                (r_s_axi_ar_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    axi_skid_buffer #(.DATA_WIDTH(RSize)) inst_r_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_s_axi_rvalid),
        .o_wr_ready               (r_s_axi_rready),
        .i_wr_data                (r_s_axi_r_pkt),
        .o_rd_valid               (s_axi_rvalid),
        .i_rd_ready               (s_axi_rready),
        .o_rd_data                ({s_axi_rid,s_axi_rdata,s_axi_rresp,s_axi_rlast,s_axi_ruser})
    );

endmodule : axi_slave_stub
