`timescale 1ns / 1ps

module axi_slave_cg
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
    parameter int TIMEOUT_B         = 1000,  // Write response channel timeout

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4  // Width of idle counter
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                          i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,

    // READ CHANNEL - Master AXI Interface (Input Side)
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

    // WRITE CHANNEL - Master AXI Interface (Input Side)
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

    // READ CHANNEL - Slave AXI Interface (Output Side to memory or backend)
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

    // WRITE CHANNEL - Slave AXI Interface (Output Side to memory or backend)
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

    // READ CHANNEL - Error outputs with FIFO interface
    output logic [3:0]                 fub_rd_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_rd_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_rd_error_id,
    output logic                       fub_rd_error_valid,
    input  logic                       fub_rd_error_ready,

    // WRITE CHANNEL - Error outputs with FIFO interface
    output logic [3:0]                 fub_wr_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_wr_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_wr_error_id,
    output logic                       fub_wr_error_valid,
    input  logic                       fub_wr_error_ready,

    // Clock gating status
    output logic                       o_rd_cg_gating,
    output logic                       o_rd_cg_idle,
    output logic                       o_wr_cg_gating,
    output logic                       o_wr_cg_idle
);

    // Instantiate the AXI slave read module with clock gating
    axi_slave_rd_cg #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R),
        .CG_IDLE_COUNT_WIDTH  (CG_IDLE_COUNT_WIDTH)
    ) i_axi_slave_rd_cg (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .i_cfg_cg_enable      (i_cfg_cg_enable),
        .i_cfg_cg_idle_count  (i_cfg_cg_idle_count),

        // Master AXI Interface (Input Side)
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

        // Slave AXI Interface (Output Side)
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

        // Error outputs with FIFO interface
        .fub_error_type       (fub_rd_error_type),
        .fub_error_addr       (fub_rd_error_addr),
        .fub_error_id         (fub_rd_error_id),
        .fub_error_valid      (fub_rd_error_valid),
        .fub_error_ready      (fub_rd_error_ready),

        // Clock gating status
        .o_cg_gating          (o_rd_cg_gating),
        .o_cg_idle            (o_rd_cg_idle)
    );

    // Instantiate the AXI slave write module with clock gating
    axi_slave_wr_cg #(
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
        .TIMEOUT_B            (TIMEOUT_B),
        .CG_IDLE_COUNT_WIDTH  (CG_IDLE_COUNT_WIDTH)
    ) i_axi_slave_wr_cg (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .i_cfg_cg_enable      (i_cfg_cg_enable),
        .i_cfg_cg_idle_count  (i_cfg_cg_idle_count),

        // Master AXI Interface (Input Side)
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

        // Slave AXI Interface (Output Side)
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

        // Error outputs with FIFO interface
        .fub_error_type       (fub_wr_error_type),
        .fub_error_addr       (fub_wr_error_addr),
        .fub_error_id         (fub_wr_error_id),
        .fub_error_valid      (fub_wr_error_valid),
        .fub_error_ready      (fub_wr_error_ready),

        // Clock gating status
        .o_cg_gating          (o_wr_cg_gating),
        .o_cg_idle            (o_wr_cg_idle)
    );

endmodule : axi_slave_cg