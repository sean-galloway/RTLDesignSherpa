`timescale 1ns / 1ps

module axil_slave_wr_cg
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

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int PW       = AXIL_PROT_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,

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
    input  logic                       fub_error_ready,

    // Clock gating status
    output logic                       cg_gating,         // Active gating indicator
    output logic                       cg_idle            // All buffers empty indicator
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals from the base module
    logic int_fub_awready;
    logic int_fub_wready;
    logic int_s_axil_bready;

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
        .gating            (cg_gating),
        .idle              (cg_idle)
    );

    // Force ready signals to 0 when clock gating is active
    assign fub_awready = cg_gating ? 1'b0 : int_fub_awready;
    assign fub_wready = cg_gating ? 1'b0 : int_fub_wready;
    assign s_axil_bready = cg_gating ? 1'b0 : int_s_axil_bready;

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
        .fub_awready         (int_fub_awready),  // Connect to internal signal

        .fub_wdata           (fub_wdata),
        .fub_wstrb           (fub_wstrb),
        .fub_wvalid          (fub_wvalid),
        .fub_wready          (int_fub_wready),   // Connect to internal signal

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
        .s_axil_bready       (int_s_axil_bready),  // Connect to internal signal

        // Error outputs
        .fub_error_type      (fub_error_type),
        .fub_error_addr      (fub_error_addr),
        .fub_error_id        (fub_error_id),
        .fub_error_valid     (fub_error_valid),
        .fub_error_ready     (fub_error_ready)
    );

endmodule : axil_slave_wr_cg
