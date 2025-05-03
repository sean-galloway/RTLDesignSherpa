`timescale 1ns / 1ps

module axil_master_rd
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXIL_PROT_WIDTH    = 3,   // Fixed for AXI-Lite

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,    // Depth of address tracking FIFO

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR        = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R         = 1000,  // Read data channel timeout

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
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
    output logic [3:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic                       int_arready;

    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [3:0]                int_r_count;

    // Flow control signal (not used in this case)
    logic                      int_block_ready;

    assign fub_arready = int_arready && !int_block_ready;
    assign fub_error_id = 'b0;

    // Instantiate base error monitor module directly
    axi_errmon_base #(
        .CHANNELS(1),             // AXI-Lite has only one channel
        .ADDR_WIDTH(AW),
        .ID_WIDTH(AXI_ID_WIDTH),  // Using minimal ID width of 1
        .TIMEOUT_ADDR(TIMEOUT_AR),
        .TIMEOUT_DATA(TIMEOUT_R),
        .TIMEOUT_RESP(0),         // Not used for read
        .ERROR_FIFO_DEPTH(ERROR_FIFO_DEPTH),
        .ADDR_FIFO_DEPTH(ADDR_FIFO_DEPTH),
        .IS_READ(1),              // This is a read monitor
        .IS_AXI(0)                // AXI-Lite, not full AXI
    ) i_axil_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Address channel signals
        .i_addr               (fub_araddr),
        .i_id                 ('0),                // No ID for AXI-Lite
        .i_valid              (fub_arvalid),
        .i_ready              (fub_arready),

        // Data channel signals
        .i_data_id            ('0),                // No ID for AXI-Lite
        .i_data_valid         (fub_rvalid),
        .i_data_ready         (fub_rready),
        .i_data_last          (1'b1),              // Always last for AXI-Lite

        // Response channel signals (unused for read)
        .i_resp_id            ('b0),
        .i_resp               ('b0),
        .i_resp_valid         ('b0),
        .i_resp_ready         ('b0),

        // Error outputs
        .o_error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .o_error_type         (fub_error_type),
        .o_error_addr         (fub_error_addr),
        .o_error_id           (),

        // Flow control
        .o_block_ready        (int_block_ready)
    );


    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                ({fub_araddr, fub_arprot}),
        .o_rd_valid               (m_axil_arvalid),
        .i_rd_ready               (m_axil_arready),
        .o_rd_count               (int_ar_count),
        .o_rd_data                ({m_axil_araddr, m_axil_arprot})
    );

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
        .o_rd_valid               (fub_rvalid),
        .i_rd_ready               (int_rready),
        .o_rd_count               (int_r_count),
        .o_rd_data                ({fub_rdata, fub_rresp})
    );

endmodule : axil_master_rd