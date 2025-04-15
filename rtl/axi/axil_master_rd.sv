`timescale 1ns / 1ps

module axil_master_rd
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
    parameter int PW       = AXIL_PROT_WIDTH,
    parameter int ARSize   = AW+PW,
    parameter int RSize    = DW+2
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    
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
    
    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;
    
    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;
    
    // Instantiate AXI-Lite read master error monitor
    axil_master_rd_errmon #(
        .AXIL_ADDR_WIDTH       (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH       (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH       (AXIL_PROT_WIDTH),
        .TIMEOUT_AR            (TIMEOUT_AR),
        .TIMEOUT_R             (TIMEOUT_R),
        .ERROR_FIFO_DEPTH      (ERROR_FIFO_DEPTH)
    ) i_axil_master_rd_errmon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        
        // AXI-Lite interface to monitor
        .m_axil_araddr         (m_axil_araddr),
        .m_axil_arprot         (m_axil_arprot),
        .m_axil_arvalid        (m_axil_arvalid),
        .m_axil_arready        (m_axil_arready),
        
        .m_axil_rdata          (m_axil_rdata),
        .m_axil_rresp          (m_axil_rresp),
        .m_axil_rvalid         (m_axil_rvalid),
        .m_axil_rready         (m_axil_rready),
        
        // Error outputs FIFO interface
        .fub_error_valid       (fub_error_valid),
        .fub_error_ready       (fub_error_ready),
        .fub_error_type        (fub_error_type),
        .fub_error_addr        (fub_error_addr),
        
        // Flow control output
        .block_ready           ()  // Not used in this implementation
    );
    
    // Connect input signals to internal wires
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
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                ({int_araddr, int_arprot}),
        .o_rd_valid               (int_skid_arvalid),
        .i_rd_ready               (int_skid_arready),
        .o_rd_count               (int_ar_count),
        .o_rd_data                (int_ar_pkt)
    );
    
    // Unpack AR signals from SKID buffer
    assign {m_axil_araddr, m_axil_arprot} = int_ar_pkt;
    assign m_axil_arvalid = int_skid_arvalid;
    assign int_skid_arready = m_axil_arready;
    
    // Instantiate R channel for read data back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axil_rvalid),
        .o_wr_ready               (m_axil_rready),
        .i_wr_data                ({m_axil_rdata, m_axil_rresp}),
        .o_rd_valid               (int_rvalid),
        .i_rd_ready               (int_rready),
        .o_rd_count               (int_r_count),
        .o_rd_data                ({int_rdata, int_rresp})
    );

endmodule : axil_master_rd