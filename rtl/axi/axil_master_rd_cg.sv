`timescale 1ns / 1ps

module axil_master_rd_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXIL_PROT_WIDTH    = 3,   // Fixed for AXI-Lite
    
    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    
    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,
    
    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR        = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R         = 1000,  // Read data channel timeout
    
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
    
    // Slave AXI-Lite Interface (Input Side)
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
    
    // Master AXI-Lite Interface (Output Side)
    // Read address channel (AR)
    output logic [AW-1:0]              m_axil_araddr,
    output logic [PW-1:0]              m_axil_arprot,
    output logic                       m_axil_arvalid,
    input  logic                       m_axil_arready,
    
    // Read data channel (R)
    input  logic [DW-1:0]              m_axil_rdata,
    input  logic [1:0]                 m_axil_rresp,
    input  logic                       m_axil_rvalid,
    output logic                       m_axil_rready,
    
    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AW-1:0]              fub_error_addr,     // Address associated with error
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
    assign user_valid = fub_arvalid || fub_rvalid || fub_error_valid;
    
    // OR all AXI-side valid signals
    assign axi_valid = m_axil_arvalid || m_axil_rvalid;
    
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
    
    // Instantiate the base AXI-Lite master read module with gated clock
    axil_master_rd #(
        .AXIL_ADDR_WIDTH     (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH     (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH     (AXIL_PROT_WIDTH),
        .SKID_DEPTH_AR       (SKID_DEPTH_AR),
        .SKID_DEPTH_R        (SKID_DEPTH_R),
        .ERROR_FIFO_DEPTH    (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR          (TIMEOUT_AR),
        .TIMEOUT_R           (TIMEOUT_R)
    ) i_axil_master_rd (
        .aclk                (gated_aclk),      // Use gated clock
        .aresetn             (aresetn),
        
        // Slave AXI-Lite interface
        .fub_araddr          (fub_araddr),
        .fub_arprot          (fub_arprot),
        .fub_arvalid         (fub_arvalid),
        .fub_arready         (fub_arready),
        
        .fub_rdata           (fub_rdata),
        .fub_rresp           (fub_rresp),
        .fub_rvalid          (fub_rvalid),
        .fub_rready          (fub_rready),
        
        // Master AXI-Lite interface
        .m_axil_araddr       (m_axil_araddr),
        .m_axil_arprot       (m_axil_arprot),
        .m_axil_arvalid      (m_axil_arvalid),
        .m_axil_arready      (m_axil_arready),
        
        .m_axil_rdata        (m_axil_rdata),
        .m_axil_rresp        (m_axil_rresp),
        .m_axil_rvalid       (m_axil_rvalid),
        .m_axil_rready       (m_axil_rready),
        
        // Error outputs
        .fub_error_type      (fub_error_type),
        .fub_error_addr      (fub_error_addr),
        .fub_error_valid     (fub_error_valid),
        .fub_error_ready     (fub_error_ready)
    );

endmodule : axil_master_rd_cg