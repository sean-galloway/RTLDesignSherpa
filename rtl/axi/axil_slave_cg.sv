`timescale 1ns / 1ps

module axil_slave_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
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
    
    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter
    
    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int PW       = AXIL_PROT_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,
    
    // Clock gating configuration
    input  logic                          i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,
    
    // Master AXI-Lite Interface (Input Side)
    // Write address channel (AW)
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [PW-1:0]              fub_awprot,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,
    
    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,
    
    // Write response channel (B)
    output logic [1:0]                 fub_bresp,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,
    
    // Read address channel (AR)
    input  logic [AW-1:0]              fub_araddr,
    input  logic [PW-1:0]              fub_arprot,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,
    
    // Read data channel (R)
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,
    
    // Slave AXI-Lite Interface (Output Side to memory/backend)
    // Write address channel (AW)
    output logic [AW-1:0]              s_axil_awaddr,
    output logic [PW-1:0]              s_axil_awprot,
    output logic                       s_axil_awvalid,
    input  logic                       s_axil_awready,
    
    // Write data channel (W)
    output logic [DW-1:0]              s_axil_wdata,
    output logic [DW/8-1:0]            s_axil_wstrb,
    output logic                       s_axil_wvalid,
    input  logic                       s_axil_wready,
    
    // Write response channel (B)
    input  logic [1:0]                 s_axil_bresp,
    input  logic                       s_axil_bvalid,
    output logic                       s_axil_bready,
    
    // Read address channel (AR)
    output logic [AW-1:0]              s_axil_araddr,
    output logic [PW-1:0]              s_axil_arprot,
    output logic                       s_axil_arvalid,
    input  logic                       s_axil_arready,
    
    // Read data channel (R)
    input  logic [DW-1:0]              s_axil_rdata,
    input  logic [1:0]                 s_axil_rresp,
    input  logic                       s_axil_rvalid,
    output logic                       s_axil_rready,
    
    // Error outputs with FIFO interface - Write
    output logic [3:0]                 fub_wr_error_type,
    output logic [AW-1:0]              fub_wr_error_addr,
    output logic                       fub_wr_error_valid,
    input  logic                       fub_wr_error_ready,
    
    // Error outputs with FIFO interface - Read
    output logic [3:0]                 fub_rd_error_type,
    output logic [AW-1:0]              fub_rd_error_addr,
    output logic                       fub_rd_error_valid,
    input  logic                       fub_rd_error_ready,
    
    // Clock gating status
    output logic                       o_wr_cg_gating,        // Write path active gating indicator
    output logic                       o_wr_cg_idle,          // Write path all buffers empty indicator
    output logic                       o_rd_cg_gating,        // Read path active gating indicator
    output logic                       o_rd_cg_idle           // Read path all buffers empty indicator
);

    // Instantiate AXI-Lite slave write clock-gated module
    axil_slave_wr_cg #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH      (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B),
        .CG_IDLE_COUNT_WIDTH  (CG_IDLE_COUNT_WIDTH)
    ) i_axil_slave_wr_cg (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        
        // Clock gating configuration
        .i_cfg_cg_enable      (i_cfg_cg_enable),
        .i_cfg_cg_idle_count  (i_cfg_cg_idle_count),
        
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
        .fub_error_valid      (fub_wr_error_valid),
        .fub_error_ready      (fub_wr_error_ready),
        
        // Clock gating status
        .o_cg_gating          (o_wr_cg_gating),
        .o_cg_idle            (o_wr_cg_idle)
    );
    
    // Instantiate AXI-Lite slave read clock-gated module
    axil_slave_rd_cg #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH      (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R),
        .CG_IDLE_COUNT_WIDTH  (CG_IDLE_COUNT_WIDTH)
    ) i_axil_slave_rd_cg (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        
        // Clock gating configuration
        .i_cfg_cg_enable      (i_cfg_cg_enable),
        .i_cfg_cg_idle_count  (i_cfg_cg_idle_count),
        
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
        .fub_error_valid      (fub_rd_error_valid),
        .fub_error_ready      (fub_rd_error_ready),
        
        // Clock gating status
        .o_cg_gating          (o_rd_cg_gating),
        .o_cg_idle            (o_rd_cg_idle)
    );

endmodule : axil_slave_cg