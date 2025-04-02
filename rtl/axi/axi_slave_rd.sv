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
    input  logic [AXI_ID_WIDTH-1:0]    fub_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    fub_rid,
    output logic [AXI_DATA_WIDTH-1:0]  fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [AXI_USER_WIDTH-1:0]  fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

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
    logic [AXI_ID_WIDTH-1:0]    int_arid;
    logic [AXI_ADDR_WIDTH-1:0]  int_araddr;
    logic [7:0]                 int_arlen;
    logic [2:0]                 int_arsize;
    logic [1:0]                 int_arburst;
    logic                       int_arlock;
    logic [3:0]                 int_arcache;
    logic [2:0]                 int_arprot;
    logic [3:0]                 int_arqos;
    logic [3:0]                 int_arregion;
    logic [AXI_USER_WIDTH-1:0]  int_aruser;
    logic                       int_arvalid;
    logic                       int_arready;

    logic [AXI_ID_WIDTH-1:0]    int_rid;
    logic [AXI_DATA_WIDTH-1:0]  int_rdata;
    logic [1:0]                 int_rresp;
    logic                       int_rlast;
    logic [AXI_USER_WIDTH-1:0]  int_ruser;
    logic                       int_rvalid;
    logic                       int_rready;

    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;

    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;

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
        .fub_arid             (fub_arid),
        .fub_araddr           (fub_araddr),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (fub_arready),

        .fub_rid              (fub_rid),
        .fub_rresp            (fub_rresp),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),
        .fub_rlast            (fub_rlast),

        // Error outputs FIFO interface
        .fub_error_valid      (fub_error_valid),
        .fub_error_ready      (fub_error_ready),
        .fub_error_type       (fub_error_type),
        .fub_error_addr       (fub_error_addr),
        .fub_error_id         (fub_error_id)
    );

    // Connect Master to Internal
    assign int_arid = fub_arid;
    assign int_araddr = fub_araddr;
    assign int_arlen = fub_arlen;
    assign int_arsize = fub_arsize;
    assign int_arburst = fub_arburst;
    assign int_arlock = fub_arlock;
    assign int_arcache = fub_arcache;
    assign int_arprot = fub_arprot;
    assign int_arqos = fub_arqos;
    assign int_arregion = fub_arregion;
    assign int_aruser = fub_aruser;
    assign int_arvalid = fub_arvalid;
    assign fub_arready = int_arready;

    assign fub_rid = int_rid;
    assign fub_rdata = int_rdata;
    assign fub_rresp = int_rresp;
    assign fub_rlast = int_rlast;
    assign fub_ruser = int_ruser;
    assign fub_rvalid = int_rvalid;
    assign int_rready = fub_rready;

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                (
            {int_arid, int_araddr, int_arlen, int_arsize,
            int_arburst, int_arlock, int_arcache, int_arprot,
            int_arqos, int_arregion, int_aruser}),
        .o_rd_valid               (int_skid_arvalid),
        .i_rd_ready               (int_skid_arready),
        .o_rd_count               (int_ar_count),
        .o_rd_data                (int_ar_pkt)
    );

    // Unpack AR signals from SKID buffer
    assign {s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst,
            s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos,
            s_axi_arregion, s_axi_aruser} = int_ar_pkt;
    assign s_axi_arvalid = int_skid_arvalid;
    assign int_skid_arready = s_axi_arready;

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
        .o_rd_valid               (int_rvalid),
        .i_rd_ready               (int_rready),
        .o_rd_count               (int_r_count),
        .o_rd_data                (
            {int_rid, int_rdata, int_rresp, int_rlast, int_ruser})
    );

endmodule : axi_slave_rd
