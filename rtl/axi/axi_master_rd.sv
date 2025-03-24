`timescale 1ns / 1ps

module axi_master_rd
#(
    // Alignment parameters
    parameter int ALIGNMENT_WIDTH = 3,  // 0:8b, 1:16b, 2:32b, 3:64b, 4:128b, 5:256b, 6:512b

    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR       = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R        = 1000,  // Read data channel timeout

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

    // Alignment boundary signal (12-bit)
    input  logic [11:0] alignment_boundary,

    // Slave AXI Interface (Input Side)
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

    // Master AXI Interface (Output Side)
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

    // Output split information with FIFO interface
    output logic [AXI_ADDR_WIDTH-1:0]  s_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    s_split_id,
    output logic [7:0]                 s_split_num_splits,
    output logic                       s_split_valid,
    input  logic                       s_split_ready,

    // Error outputs with FIFO interface
    output logic [3:0]                 s_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AXI_ADDR_WIDTH-1:0]  s_error_addr,     // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    s_error_id,       // ID associated with error
    output logic                       s_error_valid,
    input  logic                       s_error_ready
);

    // Internal connections between splitter and error monitor/skid buffer
    logic [AXI_ID_WIDTH-1:0]    int_m_axi_arid;
    logic [AXI_ADDR_WIDTH-1:0]  int_m_axi_araddr;
    logic [7:0]                 int_m_axi_arlen;
    logic [2:0]                 int_m_axi_arsize;
    logic [1:0]                 int_m_axi_arburst;
    logic                       int_m_axi_arlock;
    logic [3:0]                 int_m_axi_arcache;
    logic [2:0]                 int_m_axi_arprot;
    logic [3:0]                 int_m_axi_arqos;
    logic [3:0]                 int_m_axi_arregion;
    logic [AXI_USER_WIDTH-1:0]  int_m_axi_aruser;
    logic                       int_m_axi_arvalid;
    logic                       int_m_axi_arready;

    logic [AXI_ID_WIDTH-1:0]    int_m_axi_rid;
    logic [AXI_DATA_WIDTH-1:0]  int_m_axi_rdata;
    logic [1:0]                 int_m_axi_rresp;
    logic                       int_m_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]  int_m_axi_ruser;
    logic                       int_m_axi_rvalid;
    logic                       int_m_axi_rready;

    // SKID buffer connections
    logic [3:0]                int_m_axi_ar_count;
    logic [ARSize-1:0]         int_m_axi_ar_pkt;
    logic                      int_w_m_axi_arvalid;
    logic                      int_w_m_axi_arready;

    logic [3:0]                int_m_axi_r_count;
    logic [RSize-1:0]          int_m_axi_r_pkt;
    logic                      int_w_m_axi_rvalid;
    logic                      int_w_m_axi_rready;

    // Instantiate AXI read master splitter with FIFO interface
    axi_master_rd_splitter #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH)
    ) i_axi_master_rd_splitter (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_boundary   (alignment_boundary),

        // Slave interface (input)
        .s_axi_arid           (s_axi_arid),
        .s_axi_araddr         (s_axi_araddr),
        .s_axi_arlen          (s_axi_arlen),
        .s_axi_arsize         (s_axi_arsize),
        .s_axi_arburst        (s_axi_arburst),
        .s_axi_arlock         (s_axi_arlock),
        .s_axi_arcache        (s_axi_arcache),
        .s_axi_arprot         (s_axi_arprot),
        .s_axi_arqos          (s_axi_arqos),
        .s_axi_arregion       (s_axi_arregion),
        .s_axi_aruser         (s_axi_aruser),
        .s_axi_arvalid        (s_axi_arvalid),
        .s_axi_arready        (s_axi_arready),

        .s_axi_rid            (s_axi_rid),
        .s_axi_rdata          (s_axi_rdata),
        .s_axi_rresp          (s_axi_rresp),
        .s_axi_rlast          (s_axi_rlast),
        .s_axi_ruser          (s_axi_ruser),
        .s_axi_rvalid         (s_axi_rvalid),
        .s_axi_rready         (s_axi_rready),

        // Master interface (to error monitor)
        .m_axi_arid           (int_m_axi_arid),
        .m_axi_araddr         (int_m_axi_araddr),
        .m_axi_arlen          (int_m_axi_arlen),
        .m_axi_arsize         (int_m_axi_arsize),
        .m_axi_arburst        (int_m_axi_arburst),
        .m_axi_arlock         (int_m_axi_arlock),
        .m_axi_arcache        (int_m_axi_arcache),
        .m_axi_arprot         (int_m_axi_arprot),
        .m_axi_arqos          (int_m_axi_arqos),
        .m_axi_arregion       (int_m_axi_arregion),
        .m_axi_aruser         (int_m_axi_aruser),
        .m_axi_arvalid        (int_m_axi_arvalid),
        .m_axi_arready        (int_m_axi_arready),

        .m_axi_rid            (int_m_axi_rid),
        .m_axi_rdata          (int_m_axi_rdata),
        .m_axi_rresp          (int_m_axi_rresp),
        .m_axi_rlast          (int_m_axi_rlast),
        .m_axi_ruser          (int_m_axi_ruser),
        .m_axi_rvalid         (int_m_axi_rvalid),
        .m_axi_rready         (int_m_axi_rready),

        // Split information with FIFO interface
        .s_split_addr         (s_split_addr),
        .s_split_id           (s_split_id),
        .s_split_num_splits   (s_split_num_splits),
        .s_split_valid        (s_split_valid),
        .s_split_ready        (s_split_ready)
    );

    // Instantiate AXI read error monitor with FIFO interface
    axi_master_rd_errmon #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH)
    ) i_axi_master_rd_errmon (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // AXI interface to monitor (post-splitter)
        .m_axi_arid           (int_m_axi_arid),
        .m_axi_araddr         (int_m_axi_araddr),
        .m_axi_arvalid        (int_m_axi_arvalid),
        .m_axi_arready        (int_m_axi_arready),

        .m_axi_rid            (int_m_axi_rid),
        .m_axi_rresp          (int_m_axi_rresp),
        .m_axi_rvalid         (int_m_axi_rvalid),
        .m_axi_rready         (int_m_axi_rready),
        .m_axi_rlast          (int_m_axi_rlast),

        // Error outputs FIFO interface
        .error_valid          (s_error_valid),
        .error_ready          (s_error_ready),
        .error_type           (s_error_type),
        .error_addr           (s_error_addr),
        .error_id             (s_error_id)
    );

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_skid (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_m_axi_arvalid),
        .o_wr_ready               (int_m_axi_arready),
        .i_wr_data                (
            {int_m_axi_arid, int_m_axi_araddr, int_m_axi_arlen, int_m_axi_arsize,
            int_m_axi_arburst, int_m_axi_arlock, int_m_axi_arcache, int_m_axi_arprot,
            int_m_axi_arqos, int_m_axi_arregion, int_m_axi_aruser}),
        .o_rd_valid               (int_w_m_axi_arvalid),
        .i_rd_ready               (int_w_m_axi_arready),
        .o_rd_count               (int_m_axi_ar_count),
        .o_rd_data                (int_m_axi_ar_pkt)
    );

    // Unpack AR signals from SKID buffer
    assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
            m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
            m_axi_arregion, m_axi_aruser} = int_m_axi_ar_pkt;
    assign m_axi_arvalid = int_w_m_axi_arvalid;
    assign int_w_m_axi_arready = m_axi_arready;

    // Instantiate R channel for read data back to splitter
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_rvalid),
        .o_wr_ready               (m_axi_rready),
        .i_wr_data                ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
        .o_rd_valid               (int_m_axi_rvalid),
        .i_rd_ready               (int_m_axi_rready),
        .o_rd_count               (int_m_axi_r_count),
        .o_rd_data                (
            {int_m_axi_rid, int_m_axi_rdata, int_m_axi_rresp, int_m_axi_rlast, int_m_axi_ruser})
    );

endmodule : axi_master_rd
