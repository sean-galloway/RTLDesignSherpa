`timescale 1ns / 1ps

module axi_master_wr_cg
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AW       = 1000,  // Write address channel timeout
    parameter int TIMEOUT_W        = 1000,  // Write data channel timeout
    parameter int TIMEOUT_B        = 1000,  // Write response channel timeout

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+(DW/8)+1+UW,
    parameter int BSize    = IW+2+UW
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Clock gating configuration
    input  logic                          i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,

    // Alignment mask signal (12-bit)
    input  logic [11:0]                alignment_mask,

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [UW-1:0]              fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [UW-1:0]              fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [AXI_USER_WIDTH-1:0]  fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Output split information with FIFO interface
    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready,

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,

    // Clock gating status
    output logic                       o_cg_gating,
    output logic                       o_cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals
    logic int_awready;
    logic int_wready;
    logic int_bready;

    // OR all user-side valid signals
    assign user_valid = fub_awvalid || fub_wvalid || fub_bready || fub_split_valid || fub_error_valid;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_awvalid || m_axi_wvalid || m_axi_bvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_awready = o_cg_gating ? 1'b0 : int_awready;
    assign fub_wready = o_cg_gating ? 1'b0 : int_wready;
    assign m_axi_bready = o_cg_gating ? 1'b0 : int_bready;

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

    // Instantiate the original AXI master write module with gated clock
    axi_master_wr #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AW           (TIMEOUT_AW),
        .TIMEOUT_W            (TIMEOUT_W),
        .TIMEOUT_B            (TIMEOUT_B)
    ) i_axi_master_wr (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),
        .alignment_mask       (alignment_mask),

        // Slave AXI Interface (Input Side)
        .fub_awid             (fub_awid),
        .fub_awaddr           (fub_awaddr),
        .fub_awlen            (fub_awlen),
        .fub_awsize           (fub_awsize),
        .fub_awburst          (fub_awburst),
        .fub_awlock           (fub_awlock),
        .fub_awcache          (fub_awcache),
        .fub_awprot           (fub_awprot),
        .fub_awqos            (fub_awqos),
        .fub_awregion         (fub_awregion),
        .fub_awuser           (fub_awuser),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (int_awready),     // Connect to internal signal

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wlast            (fub_wlast),
        .fub_wuser            (fub_wuser),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (int_wready),      // Connect to internal signal

        .fub_bid              (fub_bid),
        .fub_bresp            (fub_bresp),
        .fub_buser            (fub_buser),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Master AXI Interface (Output Side)
        .m_axi_awid           (m_axi_awid),
        .m_axi_awaddr         (m_axi_awaddr),
        .m_axi_awlen          (m_axi_awlen),
        .m_axi_awsize         (m_axi_awsize),
        .m_axi_awburst        (m_axi_awburst),
        .m_axi_awlock         (m_axi_awlock),
        .m_axi_awcache        (m_axi_awcache),
        .m_axi_awprot         (m_axi_awprot),
        .m_axi_awqos          (m_axi_awqos),
        .m_axi_awregion       (m_axi_awregion),
        .m_axi_awuser         (m_axi_awuser),
        .m_axi_awvalid        (m_axi_awvalid),
        .m_axi_awready        (m_axi_awready),

        .m_axi_wdata          (m_axi_wdata),
        .m_axi_wstrb          (m_axi_wstrb),
        .m_axi_wlast          (m_axi_wlast),
        .m_axi_wuser          (m_axi_wuser),
        .m_axi_wvalid         (m_axi_wvalid),
        .m_axi_wready         (m_axi_wready),

        .m_axi_bid            (m_axi_bid),
        .m_axi_bresp          (m_axi_bresp),
        .m_axi_buser          (m_axi_buser),
        .m_axi_bvalid         (m_axi_bvalid),
        .m_axi_bready         (int_bready),      // Connect to internal signal

        // Output split information with FIFO interface
        .fub_split_addr       (fub_split_addr),
        .fub_split_id         (fub_split_id),
        .fub_split_cnt        (fub_split_cnt),
        .fub_split_valid      (fub_split_valid),
        .fub_split_ready      (fub_split_ready),

        // Error outputs with FIFO interface
        .fub_error_type       (fub_error_type),
        .fub_error_addr       (fub_error_addr),
        .fub_error_id         (fub_error_id),
        .fub_error_valid      (fub_error_valid),
        .fub_error_ready      (fub_error_ready)
    );

endmodule : axi_master_wr_cg