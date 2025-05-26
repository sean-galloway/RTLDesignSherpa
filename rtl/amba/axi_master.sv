`timescale 1ns / 1ps

module axi_master
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR        = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R         = 1000,  // Read data channel timeout
    parameter int TIMEOUT_AW        = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W         = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B         = 1000   // Write response channel timeout
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Alignment mask signals (12-bit)
    input  logic [11:0]                rd_alignment_mask,
    input  logic [11:0]                wr_alignment_mask,

    // Slave AXI Interface (Input Side)
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
    output logic [AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
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

    // Output split information with FIFO interface - Read Channel
    output logic [AXI_ADDR_WIDTH-1:0]  fub_rd_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_rd_split_id,
    output logic [7:0]                 fub_rd_split_cnt,
    output logic                       fub_rd_split_valid,
    input  logic                       fub_rd_split_ready,

    // Output split information with FIFO interface - Write Channel
    output logic [AXI_ADDR_WIDTH-1:0]  fub_wr_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_wr_split_id,
    output logic [7:0]                 fub_wr_split_cnt,
    output logic                       fub_wr_split_valid,
    input  logic                       fub_wr_split_ready,

    // Error outputs with FIFO interface - Read Channel
    output logic [3:0]                 fub_rd_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_rd_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_rd_error_id,
    output logic                       fub_rd_error_valid,
    input  logic                       fub_rd_error_ready,

    // Error outputs with FIFO interface - Write Channel
    output logic [3:0]                 fub_wr_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_wr_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_wr_error_id,
    output logic                       fub_wr_error_valid,
    input  logic                       fub_wr_error_ready
);

    // Instantiate AXI master read module
    axi_master_rd #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R)
    ) i_axi_master_rd (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_mask       (rd_alignment_mask),

        // Slave interface (input)
        .fub_arid             (fub_arid),
        .fub_araddr           (fub_araddr),
        .fub_arlen            (fub_arlen),
        .fub_arsize           (fub_arsize),
        .fub_arburst          (fub_arburst),
        .fub_arlock           (fub_arlock),
        .fub_arcache          (fub_arcache),
        .fub_arprot           (fub_arprot),
        .fub_arqos            (fub_arqos),
        .fub_arregion         (fub_arregion),
        .fub_aruser           (fub_aruser),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (fub_arready),

        .fub_rid              (fub_rid),
        .fub_rdata            (fub_rdata),
        .fub_rresp            (fub_rresp),
        .fub_rlast            (fub_rlast),
        .fub_ruser            (fub_ruser),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),

        // Master interface (output)
        .m_axi_arid           (m_axi_arid),
        .m_axi_araddr         (m_axi_araddr),
        .m_axi_arlen          (m_axi_arlen),
        .m_axi_arsize         (m_axi_arsize),
        .m_axi_arburst        (m_axi_arburst),
        .m_axi_arlock         (m_axi_arlock),
        .m_axi_arcache        (m_axi_arcache),
        .m_axi_arprot         (m_axi_arprot),
        .m_axi_arqos          (m_axi_arqos),
        .m_axi_arregion       (m_axi_arregion),
        .m_axi_aruser         (m_axi_aruser),
        .m_axi_arvalid        (m_axi_arvalid),
        .m_axi_arready        (m_axi_arready),

        .m_axi_rid            (m_axi_rid),
        .m_axi_rdata          (m_axi_rdata),
        .m_axi_rresp          (m_axi_rresp),
        .m_axi_rlast          (m_axi_rlast),
        .m_axi_ruser          (m_axi_ruser),
        .m_axi_rvalid         (m_axi_rvalid),
        .m_axi_rready         (m_axi_rready),

        // Split information with FIFO interface
        .fub_split_addr       (fub_rd_split_addr),
        .fub_split_id         (fub_rd_split_id),
        .fub_split_cnt        (fub_rd_split_cnt),
        .fub_split_valid      (fub_rd_split_valid),
        .fub_split_ready      (fub_rd_split_ready),

        // Error outputs FIFO interface
        .fub_error_valid      (fub_rd_error_valid),
        .fub_error_ready      (fub_rd_error_ready),
        .fub_error_type       (fub_rd_error_type),
        .fub_error_addr       (fub_rd_error_addr),
        .fub_error_id         (fub_rd_error_id)
    );

    // Instantiate AXI master write module
    axi_master_wr #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B)
    ) i_axi_master_wr (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_mask       (wr_alignment_mask),

        // Slave interface (input)
        .fub_awid             (fub_awid),
        .fub_awaddr           (fub_awaddr),
        .fub_awlen            (fub_awlen),
        .fub_awsize           (fub_awsize),
        .fub_awburst          (fub_awburst),
        .fub_awlock           (fub_awlock),
        .fub_awcache          (fub_awcache),
        .fub_awprot           (fub_awprot),
        .fub_awqos            (fub_awqos),
        .fub_awregion         (fub_awregion),
        .fub_awuser           (fub_awuser),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (fub_awready),

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wlast            (fub_wlast),
        .fub_wuser            (fub_wuser),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (fub_wready),

        .fub_bid              (fub_bid),
        .fub_bresp            (fub_bresp),
        .fub_buser            (fub_buser),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Master interface (output)
        .m_axi_awid           (m_axi_awid),
        .m_axi_awaddr         (m_axi_awaddr),
        .m_axi_awlen          (m_axi_awlen),
        .m_axi_awsize         (m_axi_awsize),
        .m_axi_awburst        (m_axi_awburst),
        .m_axi_awlock         (m_axi_awlock),
        .m_axi_awcache        (m_axi_awcache),
        .m_axi_awprot         (m_axi_awprot),
        .m_axi_awqos          (m_axi_awqos),
        .m_axi_awregion       (m_axi_awregion),
        .m_axi_awuser         (m_axi_awuser),
        .m_axi_awvalid        (m_axi_awvalid),
        .m_axi_awready        (m_axi_awready),

        .m_axi_wdata          (m_axi_wdata),
        .m_axi_wstrb          (m_axi_wstrb),
        .m_axi_wlast          (m_axi_wlast),
        .m_axi_wuser          (m_axi_wuser),
        .m_axi_wvalid         (m_axi_wvalid),
        .m_axi_wready         (m_axi_wready),

        .m_axi_bid            (m_axi_bid),
        .m_axi_bresp          (m_axi_bresp),
        .m_axi_buser          (m_axi_buser),
        .m_axi_bvalid         (m_axi_bvalid),
        .m_axi_bready         (m_axi_bready),

        // Split information with FIFO interface
        .fub_split_addr       (fub_wr_split_addr),
        .fub_split_id         (fub_wr_split_id),
        .fub_split_cnt        (fub_wr_split_cnt),
        .fub_split_valid      (fub_wr_split_valid),
        .fub_split_ready      (fub_wr_split_ready),

        // Error outputs FIFO interface
        .fub_error_valid      (fub_wr_error_valid),
        .fub_error_ready      (fub_wr_error_ready),
        .fub_error_type       (fub_wr_error_type),
        .fub_error_addr       (fub_wr_error_addr),
        .fub_error_id         (fub_wr_error_id)
    );

endmodule : axi_master