`timescale 1ns / 1ps

module axil_slave_wr
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

    // Slave AXI-Lite Interface (Output Side to memory or backend)
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

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections
    logic                       int_awready;

    // Flow control signal (not used in this case)
    logic                       int_block_ready;

    assign s_axil_awready = int_awready && !int_block_ready;
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

        // Address channel signals (slave interface)
        .i_addr               (fub_awaddr),
        .i_id                 ('0),                // No ID for AXI-Lite
        .i_valid              (fub_awvalid),
        .i_ready              (fub_awready),

        // Data channel signals (slave interface)
        .i_data_id            ('0),                // No ID for AXI-Lite
        .i_data_valid         (fub_wvalid),
        .i_data_ready         (fub_wready),
        .i_data_last          (1'b1),              // Always last for AXI-Lite

        // Response channel signals (slave interface)
        .i_resp_id            ('0),                // No ID for AXI-Lite
        .i_resp               (fub_bresp),
        .i_resp_valid         (fub_bvalid),
        .i_resp_ready         (fub_bready),

        // Error outputs
        .o_error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .o_error_type         (fub_error_type),
        .o_error_addr         (fub_error_addr),
        .o_error_id           (),

        // Flow control
        .o_block_ready        (int_block_ready)
    );

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AW+PW)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axil_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                ({s_axil_awaddr, s_axil_awprot}),
        .o_rd_valid               (fub_awvalid),
        .i_rd_ready               (fub_awready),
        .o_rd_count               (),
        .o_rd_data                ({fub_awaddr, fub_awprot})
    );

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(DW+(DW/8))
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axil_wvalid),
        .o_wr_ready               (s_axil_wready),
        .i_wr_data                ({s_axil_wdata, s_axil_wstrb}),
        .o_rd_valid               (fub_wvalid),
        .i_rd_ready               (fub_wready),
        .o_rd_count               (),
        .o_rd_data                ({fub_wdata, fub_wstrb})
    );

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(2)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_bvalid),
        .o_wr_ready               (fub_bready),
        .i_wr_data                (fub_bresp),
        .o_rd_valid               (s_axil_bvalid),
        .i_rd_ready               (s_axil_bready),
        .o_rd_count               (),
        .o_rd_data                (s_axil_bresp)
    );

endmodule : axil_slave_wr
