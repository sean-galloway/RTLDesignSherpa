`timescale 1ns / 1ps

module axi_slave
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
    input  logic aclk,
    input  logic aresetn,

    // READ CHANNEL - Master AXI Interface (Input Side)
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    fub_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_araddr,
    output logic [7:0]                 fub_arlen,
    output logic [2:0]                 fub_arsize,
    output logic [1:0]                 fub_arburst,
    output logic                       fub_arlock,
    output logic [3:0]                 fub_arcache,
    output logic [2:0]                 fub_arprot,
    output logic [3:0]                 fub_arqos,
    output logic [3:0]                 fub_arregion,
    output logic [AXI_USER_WIDTH-1:0]  fub_aruser,
    output logic                       fub_arvalid,
    input  logic                       fub_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    fub_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  fub_rdata,
    input  logic [1:0]                 fub_rresp,
    input  logic                       fub_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  fub_ruser,
    input  logic                       fub_rvalid,
    output logic                       fub_rready,

    // WRITE CHANNEL - Master AXI Interface (Input Side)
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
    input  logic                       fub_awready,

    // Write data channel (W)
    output logic [AXI_DATA_WIDTH-1:0]  fub_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] fub_wstrb,
    output logic                       fub_wlast,
    output logic [AXI_USER_WIDTH-1:0]  fub_wuser,
    output logic                       fub_wvalid,
    input  logic                       fub_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]    fub_bid,
    input  logic [1:0]                 fub_bresp,
    input  logic [AXI_USER_WIDTH-1:0]  fub_buser,
    input  logic                       fub_bvalid,
    output logic                       fub_bready,

    // READ CHANNEL - Slave AXI Interface (Output Side to memory or backend)
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

    // WRITE CHANNEL - Slave AXI Interface (Output Side to memory or backend)
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]  s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

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

    // Instantiate AXI slave read module
    axi_slave_rd #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R)
    ) i_axi_slave_rd (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Master interface (input)
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

        // Slave interface (output to memory/backend)
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

        // Error outputs FIFO interface
        .fub_error_valid      (fub_rd_error_valid),
        .fub_error_ready      (fub_rd_error_ready),
        .fub_error_type       (fub_rd_error_type),
        .fub_error_addr       (fub_rd_error_addr),
        .fub_error_id         (fub_rd_error_id)
    );

    // Instantiate AXI slave write module
    axi_slave_wr #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B)
    ) i_axi_slave_wr (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Master interface (input)
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

        // Slave interface (output to memory/backend)
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

        // Error outputs FIFO interface
        .fub_error_valid      (fub_wr_error_valid),
        .fub_error_ready      (fub_wr_error_ready),
        .fub_error_type       (fub_wr_error_type),
        .fub_error_addr       (fub_wr_error_addr),
        .fub_error_id         (fub_wr_error_id)
    );

endmodule : axi_slave