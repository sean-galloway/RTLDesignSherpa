`timescale 1ns / 1ps

module axi_slave_rd
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR        = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R         = 1000,  // Read data channel timeout

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Master AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    input  logic [7:0]                 m_axi_arlen,
    input  logic [2:0]                 m_axi_arsize,
    input  logic [1:0]                 m_axi_arburst,
    input  logic                       m_axi_arlock,
    input  logic [3:0]                 m_axi_arcache,
    input  logic [2:0]                 m_axi_arprot,
    input  logic [3:0]                 m_axi_arqos,
    input  logic [3:0]                 m_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_aruser,
    input  logic                       m_axi_arvalid,
    output logic                       m_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  m_axi_rdata,
    output logic [1:0]                 m_axi_rresp,
    output logic                       m_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_ruser,
    output logic                       m_axi_rvalid,
    input  logic                       m_axi_rready,

    // Slave AXI Interface (Output Side to memory or backend)
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
    output logic [7:0]                 s_axi_arlen,
    output logic [2:0]                 s_axi_arsize,
    output logic [1:0]                 s_axi_arburst,
    output logic                       s_axi_arlock,
    output logic [3:0]                 s_axi_arcache,
    output logic [2:0]                 s_axi_arprot,
    output logic [3:0]                 s_axi_arqos,
    output logic [3:0]                 s_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
    output logic                       s_axi_arvalid,
    input  logic                       s_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
    input  logic [1:0]                 s_axi_rresp,
    input  logic                       s_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
    input  logic                       s_axi_rvalid,
    output logic                       s_axi_rready,

    // Error outputs with FIFO interface
    output logic [3:0]                 m_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AXI_ADDR_WIDTH-1:0]  m_error_addr,     // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    m_error_id,       // ID associated with error
    output logic                       m_error_valid,
    input  logic                       m_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic [AXI_ID_WIDTH-1:0]    int_s_axi_arid;
    logic [AXI_ADDR_WIDTH-1:0]  int_s_axi_araddr;
    logic [7:0]                 int_s_axi_arlen;
    logic [2:0]                 int_s_axi_arsize;
    logic [1:0]                 int_s_axi_arburst;
    logic                       int_s_axi_arlock;
    logic [3:0]                 int_s_axi_arcache;
    logic [2:0]                 int_s_axi_arprot;
    logic [3:0]                 int_s_axi_arqos;
    logic [3:0]                 int_s_axi_arregion;
    logic [AXI_USER_WIDTH-1:0]  int_s_axi_aruser;
    logic                       int_s_axi_arvalid;
    logic                       int_s_axi_arready;

    logic [AXI_ID_WIDTH-1:0]    int_s_axi_rid;
    logic [AXI_DATA_WIDTH-1:0]  int_s_axi_rdata;
    logic [1:0]                 int_s_axi_rresp;
    logic                       int_s_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]  int_s_axi_ruser;
    logic                       int_s_axi_rvalid;
    logic                       int_s_axi_rready;

    // SKID buffer connections
    logic [3:0]                int_s_axi_ar_count;
    logic [ARSize-1:0]         int_s_axi_ar_pkt;
    logic                      int_w_s_axi_arvalid;
    logic                      int_w_s_axi_arready;

    logic [3:0]                int_s_axi_r_count;
    logic [RSize-1:0]          int_s_axi_r_pkt;
    logic                      int_w_s_axi_rvalid;
    logic                      int_w_s_axi_rready;

    // Instantiate AXI read slave error monitor with FIFO interface
    axi_slave_rd_errmon #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH)
    ) i_axi_slave_rd_errmon (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // AXI interface to monitor
        .m_axi_arid           (m_axi_arid),
        .m_axi_araddr         (m_axi_araddr),
        .m_axi_arvalid        (m_axi_arvalid),
        .m_axi_arready        (m_axi_arready),

        .m_axi_rid            (m_axi_rid),
        .m_axi_rresp          (m_axi_rresp),
        .m_axi_rvalid         (m_axi_rvalid),
        .m_axi_rready         (m_axi_rready),
        .m_axi_rlast          (m_axi_rlast),

        // Error outputs FIFO interface
        .error_valid          (m_error_valid),
        .error_ready          (m_error_ready),
        .error_type           (m_error_type),
        .error_addr           (m_error_addr),
        .error_id             (m_error_id)
    );

    // Connect Master to Internal
    assign int_s_axi_arid = m_axi_arid;
    assign int_s_axi_araddr = m_axi_araddr;
    assign int_s_axi_arlen = m_axi_arlen;
    assign int_s_axi_arsize = m_axi_arsize;
    assign int_s_axi_arburst = m_axi_arburst;
    assign int_s_axi_arlock = m_axi_arlock;
    assign int_s_axi_arcache = m_axi_arcache;
    assign int_s_axi_arprot = m_axi_arprot;
    assign int_s_axi_arqos = m_axi_arqos;
    assign int_s_axi_arregion = m_axi_arregion;
    assign int_s_axi_aruser = m_axi_aruser;
    assign int_s_axi_arvalid = m_axi_arvalid;
    assign m_axi_arready = int_s_axi_arready;
    
    assign m_axi_rid = int_s_axi_rid;
    assign m_axi_rdata = int_s_axi_rdata;
    assign m_axi_rresp = int_s_axi_rresp;
    assign m_axi_rlast = int_s_axi_rlast;
    assign m_axi_ruser = int_s_axi_ruser;
    assign m_axi_rvalid = int_s_axi_rvalid;
    assign int_s_axi_rready = m_axi_rready;

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_s_axi_arvalid),
        .o_wr_ready               (int_s_axi_arready),
        .i_wr_data                (
            {int_s_axi_arid, int_s_axi_araddr, int_s_axi_arlen, int_s_axi_arsize,
            int_s_axi_arburst, int_s_axi_arlock, int_s_axi_arcache, int_s_axi_arprot,
            int_s_axi_arqos, int_s_axi_arregion, int_s_axi_aruser}),
        .o_rd_valid               (int_w_s_axi_arvalid),
        .i_rd_ready               (int_w_s_axi_arready),
        .o_rd_count               (int_s_axi_ar_count),
        .o_rd_data                (int_s_axi_ar_pkt)
    );

    // Unpack AR signals from SKID buffer
    assign {s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst,
            s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos,
            s_axi_arregion, s_axi_aruser} = int_s_axi_ar_pkt;
    assign s_axi_arvalid = int_w_s_axi_arvalid;
    assign int_w_s_axi_arready = s_axi_arready;

    // Instantiate R channel for read data from memory back to the master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_rvalid),
        .o_wr_ready               (s_axi_rready),
        .i_wr_data                ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
        .o_rd_valid               (int_s_axi_rvalid),
        .i_rd_ready               (int_s_axi_rready),
        .o_rd_count               (int_s_axi_r_count),
        .o_rd_data                (
            {int_s_axi_rid, int_s_axi_rdata, int_s_axi_rresp, int_s_axi_rlast, int_s_axi_ruser})
    );

endmodule : axi_slave_rd
