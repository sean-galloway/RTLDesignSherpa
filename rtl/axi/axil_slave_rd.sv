`timescale 1ns / 1ps

module axil_slave_rd
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
    
    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int PW       = AXIL_PROT_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    
    // Master AXI-Lite Interface (Input Side)
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
    
    // Slave AXI-Lite Interface (Output Side to memory or backend)
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
    
    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AW-1:0]              fub_error_addr,     // Address associated with error
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic [AW-1:0]              int_araddr;
    logic [PW-1:0]              int_arprot;
    logic                       int_arvalid;
    logic                       int_arready;
    
    logic [DW-1:0]              int_rdata;
    logic [1:0]                 int_rresp;
    logic                       int_rvalid;
    logic                       int_rready;
    
    // Instantiate AXI-Lite read slave error monitor
    axil_slave_rd_errmon #(
        .AXIL_ADDR_WIDTH       (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH       (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH       (AXIL_PROT_WIDTH),
        .TIMEOUT_AR            (TIMEOUT_AR),
        .TIMEOUT_R             (TIMEOUT_R),
        .ERROR_FIFO_DEPTH      (ERROR_FIFO_DEPTH)
    ) i_axil_slave_rd_errmon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        
        // AXI-Lite interface to monitor
        .fub_araddr            (fub_araddr),
        .fub_arprot            (fub_arprot),
        .fub_arvalid           (fub_arvalid),
        .fub_arready           (fub_arready),
        
        .fub_rdata             (fub_rdata),
        .fub_rresp             (fub_rresp),
        .fub_rvalid            (fub_rvalid),
        .fub_rready            (fub_rready),
        
        // Error outputs FIFO interface
        .fub_error_valid       (fub_error_valid),
        .fub_error_ready       (fub_error_ready),
        .fub_error_type        (fub_error_type),
        .fub_error_addr        (fub_error_addr),
        
        // Flow control output
        .block_ready           ()  // Not used in this implementation
    );
    
    // Connect Master to Internal
    assign int_araddr = fub_araddr;
    assign int_arprot = fub_arprot;
    assign int_arvalid = fub_arvalid;
    assign fub_arready = int_arready;
    
    assign fub_rdata = int_rdata;
    assign fub_rresp = int_rresp;
    assign fub_rvalid = int_rvalid;
    assign int_rready = fub_rready;
    
    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(AW+PW)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                ({int_araddr, int_arprot}),
        .o_rd_valid               (s_axil_arvalid),
        .i_rd_ready               (s_axil_arready),
        .o_rd_count               (),
        .o_rd_data                ({s_axil_araddr, s_axil_arprot})
    );
    
    // Instantiate R channel for read data from memory back to the master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(DW+2)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axil_rvalid),
        .o_wr_ready               (s_axil_rready),
        .i_wr_data                ({s_axil_rdata, s_axil_rresp}),
        .o_rd_valid               (int_rvalid),
        .i_rd_ready               (int_rready),
        .o_rd_count               (),
        .o_rd_data                ({int_rdata, int_rresp})
    );

endmodule : axil_slave_rd