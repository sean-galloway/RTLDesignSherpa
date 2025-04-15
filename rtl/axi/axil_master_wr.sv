`timescale 1ns / 1ps

module axil_master_wr
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
    parameter int PW       = AXIL_PROT_WIDTH,
    parameter int AWSize   = AW+PW,
    parameter int WSize    = DW+(DW/8),
    parameter int BSize    = 2
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    
    // Slave AXI-Lite Interface (Input Side)
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
    
    // Master AXI-Lite Interface (Output Side)
    // Write address channel (AW)
    output logic [AW-1:0]              m_axil_awaddr,
    output logic [PW-1:0]              m_axil_awprot,
    output logic                       m_axil_awvalid,
    input  logic                       m_axil_awready,
    
    // Write data channel (W)
    output logic [DW-1:0]              m_axil_wdata,
    output logic [DW/8-1:0]            m_axil_wstrb,
    output logic                       m_axil_wvalid,
    input  logic                       m_axil_wready,
    
    // Write response channel (B)
    input  logic [1:0]                 m_axil_bresp,
    input  logic                       m_axil_bvalid,
    output logic                       m_axil_bready,
    
    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,  // Error type flags (AW timeout, W timeout, B timeout, response error)
    output logic [AW-1:0]              fub_error_addr,  // Address associated with error
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
    
    // SKID buffer connections
    logic [3:0]                int_aw_count;
    logic [AWSize-1:0]         int_aw_pkt;
    logic                      int_skid_awvalid;
    logic                      int_skid_awready;
    
    logic [3:0]                int_w_count;
    logic [WSize-1:0]          int_w_pkt;
    logic                      int_skid_wvalid;
    logic                      int_skid_wready;
    
    logic [3:0]                int_b_count;
    logic [BSize-1:0]          int_b_pkt;
    logic                      int_skid_bvalid;
    logic                      int_skid_bready;
    
    // Instantiate AXI-Lite write master error monitor
    axil_master_wr_errmon #(
        .AXIL_ADDR_WIDTH       (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH       (AXIL_DATA_WIDTH),
        .AXIL_PROT_WIDTH       (AXIL_PROT_WIDTH),
        .TIMEOUT_AW            (TIMEOUT_AW),
        .TIMEOUT_W             (TIMEOUT_W),
        .TIMEOUT_B             (TIMEOUT_B),
        .ERROR_FIFO_DEPTH      (ERROR_FIFO_DEPTH)
    ) i_axil_master_wr_errmon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        
        // AXI-Lite interface to monitor
        .m_axil_awaddr         (m_axil_awaddr),
        .m_axil_awprot         (m_axil_awprot),
        .m_axil_awvalid        (m_axil_awvalid),
        .m_axil_awready        (m_axil_awready),
        
        .m_axil_wdata          (m_axil_wdata),
        .m_axil_wstrb          (m_axil_wstrb),
        .m_axil_wvalid         (m_axil_wvalid),
        .m_axil_wready         (m_axil_wready),
        
        .m_axil_bresp          (m_axil_bresp),
        .m_axil_bvalid         (m_axil_bvalid),
        .m_axil_bready         (m_axil_bready),
        
        // Error outputs FIFO interface
        .fub_error_valid       (fub_error_valid),
        .fub_error_ready       (fub_error_ready),
        .fub_error_type        (fub_error_type),
        .fub_error_addr        (fub_error_addr),
        
        // Flow control output
        .block_ready           ()  // Not used in this implementation
    );
    
    // Connect input signals to internal wires
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
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                ({int_awaddr, int_awprot}),
        .o_rd_valid               (int_skid_awvalid),
        .i_rd_ready               (int_skid_awready),
        .o_rd_count               (int_aw_count),
        .o_rd_data                (int_aw_pkt)
    );
    
    // Unpack AW signals from SKID buffer
    assign {m_axil_awaddr, m_axil_awprot} = int_aw_pkt;
    assign m_axil_awvalid = int_skid_awvalid;
    assign int_skid_awready = m_axil_awready;
    
    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_wvalid),
        .o_wr_ready               (int_wready),
        .i_wr_data                ({int_wdata, int_wstrb}),
        .o_rd_valid               (int_skid_wvalid),
        .i_rd_ready               (int_skid_wready),
        .o_rd_count               (int_w_count),
        .o_rd_data                ({m_axil_wdata, m_axil_wstrb})
    );
    
    // Connect W signals
    assign m_axil_wvalid = int_skid_wvalid;
    assign int_skid_wready = m_axil_wready;
    
    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axil_bvalid),
        .o_wr_ready               (m_axil_bready),
        .i_wr_data                (m_axil_bresp),
        .o_rd_valid               (int_bvalid),
        .i_rd_ready               (int_bready),
        .o_rd_count               (int_b_count),
        .o_rd_data                (int_bresp)
    );

endmodule : axil_master_wr