`timescale 1ns / 1ps

module axi4_slave_wr
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+(DW/8)+1+UW,
    parameter int BSize    = IW+2+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Master AXI Interface (Input Side)
    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]    fub_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_awaddr,
    output logic [7:0]                 fub_awlen,
    output logic [2:0]                 fub_awsize,
    output logic [1:0]                 fub_awburst,
    output logic                       fub_awlock,
    output logic [3:0]                 fub_awcache,
    output logic [2:0]                 fub_awprot,
    output logic [3:0]                 fub_awqos,
    output logic [3:0]                 fub_awregion,
    output logic [AXI_USER_WIDTH-1:0]  fub_awuser,
    output logic                       fub_awvalid,
    input logic                        fub_awready,

    // Write data channel (W)
    output logic [AXI_DATA_WIDTH-1:0]  fub_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] fub_wstrb,
    output logic                       fub_wlast,
    output logic [AXI_USER_WIDTH-1:0]  fub_wuser,
    output logic                       fub_wvalid,
    input logic                        fub_wready,

    // Write response channel (B)
    input logic [AXI_ID_WIDTH-1:0]     fub_bid,
    input logic [1:0]                  fub_bresp,
    input logic [AXI_USER_WIDTH-1:0]   fub_buser,
    input logic                        fub_bvalid,
    output logic                       fub_bready,

    // Slave AXI Interface (Output Side to memory or backend)
    // Write address channel (AW)
    input logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input logic [7:0]                  s_axi_awlen,
    input logic [2:0]                  s_axi_awsize,
    input logic [1:0]                  s_axi_awburst,
    input logic                        s_axi_awlock,
    input logic [3:0]                  s_axi_awcache,
    input logic [2:0]                  s_axi_awprot,
    input logic [3:0]                  s_axi_awqos,
    input logic [3:0]                  s_axi_awregion,
    input logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input logic                        s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input logic                        s_axi_wlast,
    input logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input logic                        s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    output logic                       s_axi_bvalid,
    input logic                        s_axi_bready
);

    // Internal connections for skid buffers
    logic                      int_awready;
    logic [3:0]                int_aw_count;
    logic [3:0]                int_w_count;
    logic [3:0]                int_b_count;

    // Direct connection without error monitor flow control
    assign s_axi_awready = int_awready;

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_awvalid),
        .wr_ready               (int_awready),
        .i_wr_data                ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize,
                                    s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot,
                                    s_axi_awqos, s_axi_awregion, s_axi_awuser}),
        .rd_valid               (fub_awvalid),
        .i_rd_ready               (fub_awready),
        .rd_count               (int_aw_count),
        .rd_data                ({fub_awid, fub_awaddr, fub_awlen, fub_awsize,
                                    fub_awburst, fub_awlock, fub_awcache, fub_awprot,
                                    fub_awqos, fub_awregion, fub_awuser})
    );

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_wvalid),
        .wr_ready               (s_axi_wready),
        .i_wr_data                ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
        .rd_valid               (fub_wvalid),
        .i_rd_ready               (fub_wready),
        .rd_count               (int_w_count),
        .rd_data                ({fub_wdata, fub_wstrb, fub_wlast, fub_wuser})
    );

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_bvalid),
        .wr_ready               (fub_bready),
        .i_wr_data                ({fub_bid, fub_bresp, fub_buser}),
        .rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .rd_count               (int_b_count),
        .rd_data                ({s_axi_bid, s_axi_bresp, s_axi_buser})
    );

endmodule : axi4_slave_wr
