`timescale 1ns / 1ps

module axil_slave_wr_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXIL_PROT_WIDTH    = 3,    // Fixed for AXI-Lite
    
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
    
    // Slave AXI-Lite Interface (Output Side to memory or backend)
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
    
    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,  // Error type flags (AW timeout, W timeout, B timeout, response error)
    output logic [AW-1:0]              fub_error_addr,  // Address associated with error
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,
    
    // Clock gating status
    output logic                       o_cg_gating,         // Active gating indicator
    output logic                       o_cg_idle           // All buffers empty indicator
);

    // Gated clock signal
    logic gated_aclk;
    
    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;
    
    // OR all user-side valid signals
    assign user_valid = fub_awvalid || fub_wvalid || fub_bvalid || fub_error_valid;
    
    // OR all AXI-side valid signals
    assign axi_valid = s_axil_awvalid || s_axil_wvalid || s_axil_bvalid;
    
    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_user_valid        (user_valid),
        .i_axi_valid         (axi_valid),
        .clk_out             (gated_aclk),
        .o_gating            (o_cg_gating),
        .o_idle              (o_cg_idle)
    );
    
    // Instantiate the base AXI-Lite slave write module with gated clock
    axil_slave_wr #(
        .AXIL_ADDR_WIDTH     (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH     (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH     (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AW       (SKID_DEPTH_AW),
        .SKID_DEPTH_W        (SKID_DEPTH_W),
        .SKID_DEPTH_B        (SKID_DEPTH_B),
        .ERROR_FIFO_DEPTH    (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW          (TIMEOUT_AW),
        .TIMEOUT_W           (TIMEOUT_W),
        .TIMEOUT_B           (TIMEOUT_B)
    ) i_axil_slave_wr (
        .aclk                (gated_aclk),      // Use gated clock
        .aresetn             (aresetn),
        
        // Master AXI-Lite interface
        .fub_awaddr          (fub_awaddr),
        .fub_awprot          (fub_awprot),
        .fub_awvalid         (fub_awvalid),
        .fub_awready         (fub_awready),
        
        .fub_wdata           (fub_wdata),
        .fub_wstrb           (fub_wstrb),
        .fub_wvalid          (fub_wvalid),
        .fub_wready          (fub_wready),
        
        .fub_bresp           (fub_bresp),
        .fub_bvalid          (fub_bvalid),
        .fub_bready          (fub_bready),
        
        // Slave AXI-Lite interface
        .s_axil_awaddr       (s_axil_awaddr),
        .s_axil_awprot       (s_axil_awprot),
        .s_axil_awvalid      (s_axil_awvalid),
        .s_axil_awready      (s_axil_awready),
        
        .s_axil_wdata        (s_axil_wdata),
        .s_axil_wstrb        (s_axil_wstrb),
        .s_axil_wvalid       (s_axil_wvalid),
        .s_axil_wready       (s_axil_wready),
        
        .s_axil_bresp        (s_axil_bresp),
        .s_axil_bvalid       (s_axil_bvalid),
        .s_axil_bready       (s_axil_bready),
        
        // Error outputs
        .fub_error_type      (fub_error_type),
        .fub_error_addr      (fub_error_addr),
        .fub_error_valid     (fub_error_valid),
        .fub_error_ready     (fub_error_ready)
    );

endmodule : axil_slave_wr_cg