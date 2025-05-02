`timescale 1ns / 1ps

module axi_slave_wr
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Channel parameter
    parameter int CHANNELS          = 16,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,     // Depth of address tracking FIFO

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

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
    input logic                        s_axi_bready,

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic                      int_awready;
    logic [3:0]                int_w_count;
    logic [3:0]                int_b_count;

    // Flow control signal (not used in this case)
    logic                      int_block_ready;

    // block the arready signal when the error monitor is full
    assign s_axi_awready = int_awready && !int_block_ready;

    // Instantiate base error monitor module directly
    axi_errmon_base #(
        .CHANNELS(CHANNELS),
        .ADDR_WIDTH(AXI_ADDR_WIDTH),
        .ID_WIDTH(AXI_ID_WIDTH),
        .TIMEOUT_ADDR(TIMEOUT_AW),
        .TIMEOUT_DATA(TIMEOUT_W),
        .TIMEOUT_RESP(TIMEOUT_B),   // Used for write
        .ERROR_FIFO_DEPTH(ERROR_FIFO_DEPTH),
        .ADDR_FIFO_DEPTH(ADDR_FIFO_DEPTH),
        .IS_READ(0),                // This is a write monitor
        .IS_AXI(1)                  // Full AXI (not AXI-Lite)
    ) i_axi_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Address channel signals (slave interface)
        .i_addr               (fub_awaddr),
        .i_id                 (fub_awid),
        .i_valid              (fub_awvalid),
        .i_ready              (fub_awready),

        // Data channel signals (slave interface)
        .i_data_id            ('0),           // No ID for write data
        .i_data_valid         (fub_wvalid),
        .i_data_ready         (fub_wready),
        .i_data_last          (fub_wlast),

        // Response channel signals (slave interface)
        .i_resp_id            (fub_bid),
        .i_resp               (fub_bresp),
        .i_resp_valid         (fub_bvalid),
        .i_resp_ready         (fub_bready),

        // Error outputs
        .o_error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .o_error_type         (fub_error_type),
        .o_error_addr         (fub_error_addr),
        .o_error_id           (fub_error_id),

        // Flow control
        .o_block_ready        (int_block_ready)
    );

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize,
                                    s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot,
                                    s_axi_awqos, s_axi_awregion, s_axi_awuser}),
        .o_rd_valid               (fub_awvalid),
        .i_rd_ready               (fub_awready),
        .o_rd_count               (int_aw_count),
        .o_rd_data                ({fub_awid, fub_awaddr, fub_awlen, fub_awsize,
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
        .o_wr_ready               (s_axi_wready),
        .i_wr_data                ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
        .o_rd_valid               (fub_wvalid),
        .i_rd_ready               (fub_wready),
        .o_rd_count               (int_w_count),
        .o_rd_data                ({fub_wdata, fub_wstrb, fub_wlast, fub_wuser})
    );

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_bvalid),
        .o_wr_ready               (fub_bready),
        .i_wr_data                ({fub_bid, fub_bresp, fub_buser}),
        .o_rd_valid               (s_axi_bvalid),
        .i_rd_ready               (s_axi_bready),
        .o_rd_count               (int_b_count),
        .o_rd_data                ({s_axi_bid, s_axi_bresp, s_axi_buser})
    );

endmodule : axi_slave_wr
