`timescale 1ns / 1ps

module axil_slave
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXIL_PROT_WIDTH    = 3,    // Fixed for AXI-Lite

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout
    parameter int TIMEOUT_AR       = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R        = 1000,  // Read data channel timeout

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int PW       = AXIL_PROT_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Master AXI-Lite Interface (Input Side)
    // Write address channel (AW)
    output logic [AW-1:0]               fub_awaddr,
    output logic [PW-1:0]               fub_awprot,
    output logic                        fub_awvalid,
    input logic                         fub_awready,

    // Write data channel (W)
    output logic [DW-1:0]               fub_wdata,
    output logic [DW/8-1:0]             fub_wstrb,
    output logic                        fub_wvalid,
    input logic                         fub_wready,

    // Write response channel (B)
    input logic [1:0]                   fub_bresp,
    input logic                         fub_bvalid,
    output logic                        fub_bready,

    // Read address channel (AR)
    output logic [AW-1:0]               fub_araddr,
    output logic [PW-1:0]               fub_arprot,
    output logic                        fub_arvalid,
    input logic                         fub_arready,

    // Read data channel (R)
    input logic [DW-1:0]                fub_rdata,
    input logic [1:0]                   fub_rresp,
    input logic                         fub_rvalid,
    output logic                        fub_rready,

    // Slave AXI-Lite Interface (Output Side to memory/backend)
    // Write address channel (AW)
    input logic [AW-1:0]                s_axil_awaddr,
    input logic [PW-1:0]                s_axil_awprot,
    input logic                         s_axil_awvalid,
    output logic                        s_axil_awready,

    // Write data channel (W)
    input logic [DW-1:0]                s_axil_wdata,
    input logic [DW/8-1:0]              s_axil_wstrb,
    input logic                         s_axil_wvalid,
    output logic                        s_axil_wready,

    // Write response channel (B)
    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input logic                         s_axil_bready,

    // Read address channel (AR)
    input logic [AW-1:0]                s_axil_araddr,
    input logic [PW-1:0]                s_axil_arprot,
    input logic                         s_axil_arvalid,
    output logic                        s_axil_arready,

    // Read data channel (R)
    output logic [DW-1:0]               s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input logic                         s_axil_rready,

    // Error outputs with FIFO interface - Write
    output logic [3:0]                 fub_wr_error_type,
    output logic [AW-1:0]              fub_wr_error_addr,
    output logic [IW-1:0]              fub_wr_error_id,
    output logic                       fub_wr_error_valid,
    input  logic                       fub_wr_error_ready,

    // Error outputs with FIFO interface - Read
    output logic [3:0]                 fub_rd_error_type,
    output logic [AW-1:0]              fub_rd_error_addr,
    output logic [IW-1:0]              fub_rd_error_id,
    output logic                       fub_rd_error_valid,
    input  logic                       fub_rd_error_ready
);

    // Instantiate AXI-Lite slave write module
    axil_slave_wr #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH      (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B)
    ) i_axil_slave_wr (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Master AXI-Lite interface
        .fub_awaddr           (fub_awaddr),
        .fub_awprot           (fub_awprot),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (fub_awready),

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (fub_wready),

        .fub_bresp            (fub_bresp),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Slave AXI-Lite interface
        .s_axil_awaddr        (s_axil_awaddr),
        .s_axil_awprot        (s_axil_awprot),
        .s_axil_awvalid       (s_axil_awvalid),
        .s_axil_awready       (s_axil_awready),

        .s_axil_wdata         (s_axil_wdata),
        .s_axil_wstrb         (s_axil_wstrb),
        .s_axil_wvalid        (s_axil_wvalid),
        .s_axil_wready        (s_axil_wready),

        .s_axil_bresp         (s_axil_bresp),
        .s_axil_bvalid        (s_axil_bvalid),
        .s_axil_bready        (s_axil_bready),

        // Error outputs
        .fub_error_type       (fub_wr_error_type),
        .fub_error_addr       (fub_wr_error_addr),
        .fub_error_id         (fub_wr_error_id),
        .fub_error_valid      (fub_wr_error_valid),
        .fub_error_ready      (fub_wr_error_ready)
    );

    // Instantiate AXI-Lite slave read module
    axil_slave_rd #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH      (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R)
    ) i_axil_slave_rd (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Master AXI-Lite interface
        .fub_araddr           (fub_araddr),
        .fub_arprot           (fub_arprot),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (fub_arready),

        .fub_rdata            (fub_rdata),
        .fub_rresp            (fub_rresp),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),

        // Slave AXI-Lite interface
        .s_axil_araddr        (s_axil_araddr),
        .s_axil_arprot        (s_axil_arprot),
        .s_axil_arvalid       (s_axil_arvalid),
        .s_axil_arready       (s_axil_arready),

        .s_axil_rdata         (s_axil_rdata),
        .s_axil_rresp         (s_axil_rresp),
        .s_axil_rvalid        (s_axil_rvalid),
        .s_axil_rready        (s_axil_rready),

        // Error outputs
        .fub_error_type       (fub_rd_error_type),
        .fub_error_addr       (fub_rd_error_addr),
        .fub_error_id         (fub_rd_error_id),
        .fub_error_valid      (fub_rd_error_valid),
        .fub_error_ready      (fub_rd_error_ready)
    );

endmodule : axil_slave
