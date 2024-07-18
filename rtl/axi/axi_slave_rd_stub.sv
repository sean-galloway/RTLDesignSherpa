`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi_slave_rd_stub
#(
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
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

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
    // AR interface
    output logic                       r_s_axi_arvalid,
    input  logic                       r_s_axi_arready,
    output logic [3:0]                 r_s_axi_ar_count,
    output logic [ARSize-1:0]          r_s_axi_ar_pkt,

    // R interface
    input  logic                       r_s_axi_rvalid,
    output logic                       r_s_axi_rready,
    input  logic [RSize-1:0]           r_s_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize)) inst_ar_phase (
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
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_R), .DATA_WIDTH(RSize)) inst_r_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_s_axi_rvalid),
        .o_wr_ready               (r_s_axi_rready),
        .i_wr_data                (r_s_axi_r_pkt),
        .o_rd_valid               (s_axi_rvalid),
        .i_rd_ready               (s_axi_rready),
        .o_rd_data                ({s_axi_rid,s_axi_rdata,s_axi_rresp,s_axi_rlast,s_axi_ruser})
    );

endmodule : axi_slave_rd_stub
