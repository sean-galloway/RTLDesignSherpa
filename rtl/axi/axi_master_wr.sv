`timescale 1ns / 1ps

module axi_master_wr
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
    parameter int SPLIT_FIFO_DEPTH  = 2,
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
    input  logic                       aclk,
    input  logic                       aresetn,

    // Alignment mask signal (12-bit)
    input  logic [11:0]                alignment_mask,

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              s_axi_awid,
    input  logic [AW-1:0]              s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [UW-1:0]              s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              s_axi_wdata,
    input  logic [DW/8-1:0]            s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [UW-1:0]              s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Output split information with FIFO interface
    output logic [AW-1:0]              s_split_addr,
    output logic [IW-1:0]              s_split_id,
    output logic [7:0]                 s_split_cnt,
    output logic                       s_split_valid,
    input  logic                       s_split_ready,

    // Error outputs with FIFO interface
                        // Error type flags (AW timeout, W timeout, B timeout, response error)
    output logic [3:0]                 s_error_type,
    output logic [AW-1:0]              s_error_addr,     // Address associated with error
    output logic [IW-1:0]              s_error_id,       // ID associated with error
    output logic                       s_error_valid,
    input  logic                       s_error_ready
);

    // Internal connections between splitter and error monitor/skid buffer
    logic [IW-1:0]              int_m_axi_awid;
    logic [AW-1:0]              int_m_axi_awaddr;
    logic [7:0]                 int_m_axi_awlen;
    logic [2:0]                 int_m_axi_awsize;
    logic [1:0]                 int_m_axi_awburst;
    logic                       int_m_axi_awlock;
    logic [3:0]                 int_m_axi_awcache;
    logic [2:0]                 int_m_axi_awprot;
    logic [3:0]                 int_m_axi_awqos;
    logic [3:0]                 int_m_axi_awregion;
    logic [UW-1:0]              int_m_axi_awuser;
    logic                       int_m_axi_awvalid;
    logic                       int_m_axi_awready;

    logic [DW-1:0]              int_m_axi_wdata;
    logic [DW/8-1:0]            int_m_axi_wstrb;
    logic                       int_m_axi_wlast;
    logic [UW-1:0]              int_m_axi_wuser;
    logic                       int_m_axi_wvalid;
    logic                       int_m_axi_wready;

    logic [IW-1:0]              int_m_axi_bid;
    logic [1:0]                 int_m_axi_bresp;
    logic [UW-1:0]              int_m_axi_buser;
    logic                       int_m_axi_bvalid;
    logic                       int_m_axi_bready;

    // SKID buffer connections
    logic [3:0]                int_m_axi_aw_count;
    logic [AWSize-1:0]         int_m_axi_aw_pkt;
    logic                      int_w_m_axi_awvalid;
    logic                      int_w_m_axi_awready;

    logic [3:0]                int_m_axi_w_count;
    logic [WSize-1:0]          int_m_axi_w_pkt;
    logic                      int_w_m_axi_wvalid;
    logic                      int_w_m_axi_wready;

    logic [3:0]                int_m_axi_b_count;
    logic [BSize-1:0]          int_m_axi_b_pkt;
    logic                      int_w_m_axi_bvalid;
    logic                      int_w_m_axi_bready;

    // Instantiate AXI write master splitter with FIFO interface
    axi_master_wr_splitter #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH)
    ) i_axi_master_wr_splitter (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_mask       (alignment_mask),

        // Slave interface (input)
        .s_axi_awid           (s_axi_awid),
        .s_axi_awaddr         (s_axi_awaddr),
        .s_axi_awlen          (s_axi_awlen),
        .s_axi_awsize         (s_axi_awsize),
        .s_axi_awburst        (s_axi_awburst),
        .s_axi_awlock         (s_axi_awlock),
        .s_axi_awcache        (s_axi_awcache),
        .s_axi_awprot         (s_axi_awprot),
        .s_axi_awqos          (s_axi_awqos),
        .s_axi_awregion       (s_axi_awregion),
        .s_axi_awuser         (s_axi_awuser),
        .s_axi_awvalid        (s_axi_awvalid),
        .s_axi_awready        (s_axi_awready),

        .s_axi_wdata          (s_axi_wdata),
        .s_axi_wstrb          (s_axi_wstrb),
        .s_axi_wlast          (s_axi_wlast),
        .s_axi_wuser          (s_axi_wuser),
        .s_axi_wvalid         (s_axi_wvalid),
        .s_axi_wready         (s_axi_wready),

        .s_axi_bid            (s_axi_bid),
        .s_axi_bresp          (s_axi_bresp),
        .s_axi_buser          (s_axi_buser),
        .s_axi_bvalid         (s_axi_bvalid),
        .s_axi_bready         (s_axi_bready),

        // Master interface (to error monitor)
        .m_axi_awid           (int_m_axi_awid),
        .m_axi_awaddr         (int_m_axi_awaddr),
        .m_axi_awlen          (int_m_axi_awlen),
        .m_axi_awsize         (int_m_axi_awsize),
        .m_axi_awburst        (int_m_axi_awburst),
        .m_axi_awlock         (int_m_axi_awlock),
        .m_axi_awcache        (int_m_axi_awcache),
        .m_axi_awprot         (int_m_axi_awprot),
        .m_axi_awqos          (int_m_axi_awqos),
        .m_axi_awregion       (int_m_axi_awregion),
        .m_axi_awuser         (int_m_axi_awuser),
        .m_axi_awvalid        (int_m_axi_awvalid),
        .m_axi_awready        (int_m_axi_awready),

        .m_axi_wdata          (int_m_axi_wdata),
        .m_axi_wstrb          (int_m_axi_wstrb),
        .m_axi_wlast          (int_m_axi_wlast),
        .m_axi_wuser          (int_m_axi_wuser),
        .m_axi_wvalid         (int_m_axi_wvalid),
        .m_axi_wready         (int_m_axi_wready),

        .m_axi_bid            (int_m_axi_bid),
        .m_axi_bresp          (int_m_axi_bresp),
        .m_axi_buser          (int_m_axi_buser),
        .m_axi_bvalid         (int_m_axi_bvalid),
        .m_axi_bready         (int_m_axi_bready),

        // Split information with FIFO interface
        .s_split_addr         (s_split_addr),
        .s_split_id           (s_split_id),
        .s_split_cnt          (s_split_cnt),
        .s_split_valid        (s_split_valid),
        .s_split_ready        (s_split_ready)
    );

    // Instantiate AXI write error monitor with FIFO interface
    axi_master_wr_errmon #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH)
    ) i_axi_master_wr_errmon (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // AXI interface to monitor (post-splitter)
        .m_axi_awid           (int_m_axi_awid),
        .m_axi_awaddr         (int_m_axi_awaddr),
        .m_axi_awvalid        (int_m_axi_awvalid),
        .m_axi_awready        (int_m_axi_awready),

        .m_axi_wvalid         (int_m_axi_wvalid),
        .m_axi_wready         (int_m_axi_wready),
        .m_axi_wlast          (int_m_axi_wlast),

        .m_axi_bid            (int_m_axi_bid),
        .m_axi_bresp          (int_m_axi_bresp),
        .m_axi_bvalid         (int_m_axi_bvalid),
        .m_axi_bready         (int_m_axi_bready),

        // Error outputs FIFO interface
        .error_valid          (s_error_valid),
        .error_ready          (s_error_ready),
        .error_type           (s_error_type),
        .error_addr           (s_error_addr),
        .error_id             (s_error_id)
    );

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_m_axi_awvalid),
        .o_wr_ready               (int_m_axi_awready),
        .i_wr_data                (
            {int_m_axi_awid, int_m_axi_awaddr, int_m_axi_awlen, int_m_axi_awsize,
            int_m_axi_awburst, int_m_axi_awlock, int_m_axi_awcache, int_m_axi_awprot,
            int_m_axi_awqos, int_m_axi_awregion, int_m_axi_awuser}),
        .o_rd_valid               (int_w_m_axi_awvalid),
        .i_rd_ready               (int_w_m_axi_awready),
        .o_rd_count               (int_m_axi_aw_count),
        .o_rd_data                (int_m_axi_aw_pkt)
    );

    // Unpack AW signals from SKID buffer
    assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
            m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
            m_axi_awregion, m_axi_awuser} = int_m_axi_aw_pkt;
    assign m_axi_awvalid = int_w_m_axi_awvalid;
    assign int_w_m_axi_awready = m_axi_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_m_axi_wvalid),
        .o_wr_ready               (int_m_axi_wready),
        .i_wr_data                (
            {int_m_axi_wdata, int_m_axi_wstrb, int_m_axi_wlast, int_m_axi_wuser}),
        .o_rd_valid               (int_w_m_axi_wvalid),
        .i_rd_ready               (int_w_m_axi_wready),
        .o_rd_count               (int_m_axi_w_count),
        .o_rd_data                (int_m_axi_w_pkt)
    );

    // Unpack W signals from SKID buffer
    assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser} = int_m_axi_w_pkt;
    assign m_axi_wvalid = int_w_m_axi_wvalid;
    assign int_w_m_axi_wready = m_axi_wready;

    // Instantiate B channel for write response back to splitter
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_bvalid),
        .o_wr_ready               (m_axi_bready),
        .i_wr_data                ({m_axi_bid, m_axi_bresp, m_axi_buser}),
        .o_rd_valid               (int_m_axi_bvalid),
        .i_rd_ready               (int_m_axi_bready),
        .o_rd_count               (int_m_axi_b_count),
        .o_rd_data                ({int_m_axi_bid, int_m_axi_bresp, int_m_axi_buser})
    );

endmodule : axi_master_wr
