`timescale 1ns / 1ps

module axi_master_wr_stub
#(
    parameter int SKID_DEPTH_AW          = 2,
    parameter int SKID_DEPTH_W           = 4,
    parameter int SKID_DEPTH_B           = 2,

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
    parameter int BSize    = IW+2+UW
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
    output logic [BSize-1:0]           r_m_axi_b_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_AW), .DATA_WIDTH(AWSize)) inst_aw_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_m_axi_awvalid),
        .o_wr_ready               (r_m_axi_awready),
        .i_wr_data                (r_m_axi_aw_pkt),
        .o_rd_valid               (m_axi_awvalid),
        .i_rd_ready               (m_axi_awready),
        .o_rd_count               (r_m_axi_aw_count),
        .o_rd_data                ({m_axi_awid,m_axi_awaddr,m_axi_awlen,m_axi_awsize,m_axi_awburst,
                                    m_axi_awlock,m_axi_awcache,m_axi_awprot,m_axi_awqos,
                                    m_axi_awregion,m_axi_awuser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_W), .DATA_WIDTH(WSize)) inst_w_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (r_m_axi_wvalid),
        .o_wr_ready               (r_m_axi_wready),
        .i_wr_data                (r_m_axi_w_pkt),
        .o_rd_valid               (m_axi_wvalid),
        .i_rd_ready               (m_axi_wready),
        .o_rd_data                ({m_axi_wdata,m_axi_wstrb,m_axi_wlast,m_axi_wuser})
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    axi_skid_buffer #(.SKID_DEPTH(SKID_DEPTH_B), .DATA_WIDTH(BSize)) inst_b_phase (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_bvalid),
        .o_wr_ready               (m_axi_bready),
        .i_wr_data                ({m_axi_bid,m_axi_bresp,m_axi_buser}),
        .o_rd_valid               (r_m_axi_bvalid),
        .i_rd_ready               (r_m_axi_bready),
        .o_rd_data                (r_m_axi_b_pkt)
    );

endmodule : axi_master_wr_stub
