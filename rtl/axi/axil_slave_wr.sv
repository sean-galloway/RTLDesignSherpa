`timescale 1ns / 1ps

module axil_slave_wr
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
    output logic [3:0]                 fub_error_type,     // Error type flags (AW timeout, W timeout, B timeout, response error)
    output logic [AW-1:0]              fub_error_addr,     // Address associated with error
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections
    logic [AW-1:0]              int_awaddr;
    logic [PW-1:0]              int_awprot;
    logic                       int_awvalid;
    logic                       int_awready;
    
    logic [DW-1:0]              int_wdata;
    logic [DW/8-1:0]            int_wstrb;
    logic                       int_wvalid;
    logic                       int_wready;
    
    logic [1:0]                 int_bresp;
    logic                       int_bvalid;
    logic                       int_bready;
    
    // Instantiate AXI-Lite write slave error monitor
    axil_slave_wr_errmon #(
        .AXIL_ADDR_WIDTH       (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH       (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH       (AXIL_PROT_WIDTH),
        .TIMEOUT_AW            (TIMEOUT_AW),
        .TIMEOUT_W             (TIMEOUT_W),
        .TIMEOUT_B             (TIMEOUT_B),
        .ERROR_FIFO_DEPTH      (ERROR_FIFO_DEPTH)
    ) i_axil_slave_wr_errmon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        
        // AXI-Lite interface to monitor
        .fub_awaddr            (fub_awaddr),
        .fub_awprot            (fub_awprot),
        .fub_awvalid           (fub_awvalid),
        .fub_awready           (fub_awready),
        
        .fub_wdata             (fub_wdata),
        .fub_wstrb             (fub_wstrb),
        .fub_wvalid            (fub_wvalid),
        .fub_wready            (fub_wready),
        
        .fub_bresp             (fub_bresp),
        .fub_bvalid            (fub_bvalid),
        .fub_bready            (fub_bready),
        
        // Error outputs FIFO interface
        .fub_error_valid       (fub_error_valid),
        .fub_error_ready       (fub_error_ready),
        .fub_error_type        (fub_error_type),
        .fub_error_addr        (fub_error_addr),
        
        // Flow control output
        .block_ready           ()  // Not used in this implementation
    );
    
    // Connect Master to Internal
    assign int_awaddr = fub_awaddr;
    assign int_awprot = fub_awprot;
    assign int_awvalid = fub_awvalid;
    assign fub_awready = int_awready;
    
    assign int_wdata = fub_wdata;
    assign int_wstrb = fub_wstrb;
    assign int_wvalid = fub_wvalid;
    assign fub_wready = int_wready;
    
    assign fub_bresp = int_bresp;
    assign fub_bvalid = int_bvalid;
    assign int_bready = fub_bready;
    
    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AW+PW)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                ({int_awaddr, int_awprot}),
        .o_rd_valid               (s_axil_awvalid),
        .i_rd_ready               (s_axil_awready),
        .o_rd_count               (),
        .o_rd_data                ({s_axil_awaddr, s_axil_awprot})
    );
    
    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(DW+(DW/8))
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_wvalid),
        .o_wr_ready               (int_wready),
        .i_wr_data                ({int_wdata, int_wstrb}),
        .o_rd_valid               (s_axil_wvalid),
        .i_rd_ready               (s_axil_wready),
        .o_rd_count               (),
        .o_rd_data                ({s_axil_wdata, s_axil_wstrb})
    );
    
    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(2)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axil_bvalid),
        .o_wr_ready               (s_axil_bready),
        .i_wr_data                (s_axil_bresp),
        .o_rd_valid               (int_bvalid),
        .i_rd_ready               (int_bready),
        .o_rd_count               (),
        .o_rd_data                (int_bresp)
    );

endmodule : axil_slave_wr