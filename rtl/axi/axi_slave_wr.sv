`timescale 1ns / 1ps

module axi_slave_wr
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

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,

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
    input  logic [AXI_ID_WIDTH-1:0]    fub_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [AXI_USER_WIDTH-1:0]  fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]  fub_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [AXI_USER_WIDTH-1:0]  fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [AXI_USER_WIDTH-1:0]  fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Slave AXI Interface (Output Side to memory or backend)
    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
    output logic [7:0]                 s_axi_awlen,
    output logic [2:0]                 s_axi_awsize,
    output logic [1:0]                 s_axi_awburst,
    output logic                       s_axi_awlock,
    output logic [3:0]                 s_axi_awcache,
    output logic [2:0]                 s_axi_awprot,
    output logic [3:0]                 s_axi_awqos,
    output logic [3:0]                 s_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_awuser,
    output logic                       s_axi_awvalid,
    input  logic                       s_axi_awready,

    // Write data channel (W)
    output logic [AXI_DATA_WIDTH-1:0]  s_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    output logic                       s_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_wuser,
    output logic                       s_axi_wvalid,
    input  logic                       s_axi_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    input  logic [1:0]                 s_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    input  logic                       s_axi_bvalid,
    output logic                       s_axi_bready,

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,     // Error type flags (AW timeout, W timeout, B timeout, response error)
    output logic [AXI_ADDR_WIDTH-1:0]  fub_error_addr,     // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id,       // ID associated with error
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic [AXI_ID_WIDTH-1:0]    int_awid;
    logic [AXI_ADDR_WIDTH-1:0]  int_awaddr;
    logic [7:0]                 int_awlen;
    logic [2:0]                 int_awsize;
    logic [1:0]                 int_awburst;
    logic                       int_awlock;
    logic [3:0]                 int_awcache;
    logic [2:0]                 int_awprot;
    logic [3:0]                 int_awqos;
    logic [3:0]                 int_awregion;
    logic [AXI_USER_WIDTH-1:0]  int_awuser;
    logic                       int_awvalid;
    logic                       int_awready;

    logic [AXI_DATA_WIDTH-1:0]  int_wdata;
    logic [AXI_DATA_WIDTH/8-1:0] int_wstrb;
    logic                       int_wlast;
    logic [AXI_USER_WIDTH-1:0]  int_wuser;
    logic                       int_wvalid;
    logic                       int_wready;

    logic [AXI_ID_WIDTH-1:0]    int_bid;
    logic [1:0]                 int_bresp;
    logic [AXI_USER_WIDTH-1:0]  int_buser;
    logic                       int_bvalid;
    logic                       int_bready;

    // SKID buffer connections
    logic [3:0]                int_aw_count;
    logic [AWSize-1:0]         int_aw_pkt;
    logic                      int_skid_awvalid;
    logic                      int_skid_awready;

    logic [3:0]                int_w_count;
    logic [WSize-1:0]          int_w_pkt;
    logic                      int_skid_wvalid;
    logic                      int_skid_wready;

    logic [3:0]                int_b_count;
    logic [BSize-1:0]          int_b_pkt;
    logic                      int_skid_bvalid;
    logic                      int_skid_bready;

    // Instantiate AXI write slave error monitor with FIFO interface
    axi_slave_wr_errmon #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH)
    ) i_axi_slave_wr_errmon (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // AXI interface to monitor
        .fub_awid             (fub_awid),
        .fub_awaddr           (fub_awaddr),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (fub_awready),

        .fub_wvalid           (fub_wvalid),
        .fub_wready           (fub_wready),
        .fub_wlast            (fub_wlast),

        .fub_bid              (fub_bid),
        .fub_bresp            (fub_bresp),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Error outputs FIFO interface
        .fub_error_valid      (fub_error_valid),
        .fub_error_ready      (fub_error_ready),
        .fub_error_type       (fub_error_type),
        .fub_error_addr       (fub_error_addr),
        .fub_error_id         (fub_error_id)
    );

    // Connect Master to Internal
    assign int_awid = fub_awid;
    assign int_awaddr = fub_awaddr;
    assign int_awlen = fub_awlen;
    assign int_awsize = fub_awsize;
    assign int_awburst = fub_awburst;
    assign int_awlock = fub_awlock;
    assign int_awcache = fub_awcache;
    assign int_awprot = fub_awprot;
    assign int_awqos = fub_awqos;
    assign int_awregion = fub_awregion;
    assign int_awuser = fub_awuser;
    assign int_awvalid = fub_awvalid;
    assign fub_awready = int_awready;

    assign int_wdata = fub_wdata;
    assign int_wstrb = fub_wstrb;
    assign int_wlast = fub_wlast;
    assign int_wuser = fub_wuser;
    assign int_wvalid = fub_wvalid;
    assign fub_wready = int_wready;

    assign fub_bid = int_bid;
    assign fub_bresp = int_bresp;
    assign fub_buser = int_buser;
    assign fub_bvalid = int_bvalid;
    assign int_bready = fub_bready;

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                (
            {int_awid, int_awaddr, int_awlen, int_awsize,
            int_awburst, int_awlock, int_awcache, int_awprot,
            int_awqos, int_awregion, int_awuser}),
        .o_rd_valid               (int_skid_awvalid),
        .i_rd_ready               (int_skid_awready),
        .o_rd_count               (int_aw_count),
        .o_rd_data                (int_aw_pkt)
    );

    // Unpack AW signals from SKID buffer
    assign {s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst,
            s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos,
            s_axi_awregion, s_axi_awuser} = int_aw_pkt;
    assign s_axi_awvalid = int_skid_awvalid;
    assign int_skid_awready = s_axi_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_wvalid),
        .o_wr_ready               (int_wready),
        .i_wr_data                (
            {int_wdata, int_wstrb, int_wlast, int_wuser}),
        .o_rd_valid               (int_skid_wvalid),
        .i_rd_ready               (int_skid_wready),
        .o_rd_count               (int_w_count),
        .o_rd_data                (int_w_pkt)
    );

    // Unpack W signals from SKID buffer
    assign {s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser} = int_w_pkt;
    assign s_axi_wvalid = int_skid_wvalid;
    assign int_skid_wready = s_axi_wready;

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_bvalid),
        .o_wr_ready               (s_axi_bready),
        .i_wr_data                ({s_axi_bid, s_axi_bresp, s_axi_buser}),
        .o_rd_valid               (int_bvalid),
        .i_rd_ready               (int_bready),
        .o_rd_count               (int_b_count),
        .o_rd_data                ({int_bid, int_bresp, int_buser})
    );

endmodule : axi_slave_wr