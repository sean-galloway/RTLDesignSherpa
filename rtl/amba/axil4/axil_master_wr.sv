`timescale 1ns / 1ps

module axil_master_wr
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

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,     // Depth of address tracking FIFO

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
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
    output logic [3:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections
    logic                       int_awready;

    // SKID buffer connections
    logic [3:0]                int_aw_count;
    logic [3:0]                int_w_count;

    logic [3:0]                int_b_count;

    // Flow control signal (not used in this case)
    logic                      int_block_ready;

    assign fub_awready = int_awready && !int_block_ready;
    assign fub_error_id = 'b0;


    // Instantiate base error monitor module directly
    axi_errmon_base #(
        .CHANNELS(1),             // AXI-Lite has only one channel
        .ADDR_WIDTH(AW),
        .ID_WIDTH(AXI_ID_WIDTH),  // Using minimal ID width of 1
        .TIMEOUT_ADDR(TIMEOUT_AW),
        .TIMEOUT_DATA(TIMEOUT_W),
        .TIMEOUT_RESP(TIMEOUT_B),  // Used for write
        .ERROR_FIFO_DEPTH(ERROR_FIFO_DEPTH),
        .ADDR_FIFO_DEPTH(ADDR_FIFO_DEPTH),
        .IS_READ(0),               // This is a write monitor
        .IS_AXI(0)                 // AXI-Lite, not full AXI
    ) i_axil_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Address channel signals
        .i_addr               (fub_awaddr),
        .i_id                 ('0),                // No ID for AXI-Lite
        .i_valid              (fub_awvalid),
        .i_ready              (fub_awready),

        // Data channel signals
        .i_data_id            ('0),                // No ID for AXI-Lite
        .i_data_valid         (fub_wvalid),
        .i_data_ready         (fub_wready),
        .i_data_last          (1'b1),              // Always last for AXI-Lite

        // Response channel signals
        .i_resp_id            ('0),                // No ID for AXI-Lite
        .i_resp               (fub_bresp),
        .i_resp_valid         (fub_bvalid),
        .i_resp_ready         (fub_bready),

        // Error outputs
        .error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .error_type         (fub_error_type),
        .error_addr         (fub_error_addr),
        .error_id           (),

        // Flow control
        .block_ready        (int_block_ready)
    );


    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_awvalid),
        .wr_ready               (int_awready),
        .i_wr_data                ({fub_awaddr, fub_awprot}),
        .rd_valid               (m_axil_awvalid),
        .i_rd_ready               (m_axil_awready),
        .rd_count               (int_aw_count),
        .rd_data                ({m_axil_awaddr, m_axil_awprot})
    );

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_wvalid),
        .wr_ready               (fub_wready),
        .i_wr_data                ({fub_wdata, fub_wstrb}),
        .rd_valid               (m_axil_wvalid),
        .i_rd_ready               (m_axil_wready),
        .rd_count               (int_w_count),
        .rd_data                ({m_axil_wdata, m_axil_wstrb})
    );

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axil_bvalid),
        .wr_ready               (m_axil_bready),
        .i_wr_data                (m_axil_bresp),
        .rd_valid               (fub_bvalid),
        .i_rd_ready               (fub_bready),
        .rd_count               (fub_b_count),
        .rd_data                (fub_bresp)
    );

endmodule : axil_master_wr
