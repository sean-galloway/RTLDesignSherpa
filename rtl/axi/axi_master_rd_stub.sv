`timescale 1ns / 1ps

module axi_master_rd_stub
#(
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
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

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
    // AR interface
    input  logic                       r_m_axi_arvalid,
    output logic                       r_m_axi_arready,
    input  logic [3:0]                 r_m_axi_ar_count,
    input  logic [ARSize-1:0]          r_m_axi_ar_pkt,

    // R interface
    output logic                       r_m_axi_rvalid,
    input  logic                       r_m_axi_rready,
    output logic [RSize-1:0]           r_m_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize)) inst_ar_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_arvalid),
        .o_wr_ready               (m_axi_arready),
        .i_wr_data                ({m_axi_arid,m_axi_araddr,m_axi_arlen,m_axi_arsize,m_axi_arburst,
                                    m_axi_arlock,m_axi_arcache,m_axi_arprot,m_axi_arqos,
                                    m_axi_arregion,m_axi_aruser}),
        .o_rd_valid               (r_m_axi_arvalid),
        .i_rd_ready               (r_m_axi_arready),
        .o_rd_count               (r_m_axi_ar_count),
        .o_rd_data                (r_m_axi_ar_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_R), .DATA_WIDTH(RSize)) inst_r_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_m_axi_rvalid),
        .o_wr_ready               (r_m_axi_rready),
        .i_wr_data                (r_m_axi_r_pkt),
        .o_rd_valid               (m_axi_rvalid),
        .i_rd_ready               (m_axi_rready),
        .o_rd_data                ({m_axi_rid,m_axi_rdata,m_axi_rresp,m_axi_rlast,m_axi_ruser})
    );

endmodule : axi_master_rd_stub
