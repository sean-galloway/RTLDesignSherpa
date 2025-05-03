`timescale 1ns / 1ps

module axi_master_rd_cg
#(
    // Alignment parameters
    parameter int ALIGNMENT_WIDTH = 3,  // 0:8b, 1:16b, 2:32b, 3:64b, 4:128b, 5:256b, 6:512b

    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR       = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R        = 1000,  // Read data channel timeout

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                          i_cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] i_cfg_cg_idle_count,

    // Alignment mask signal (12-bit)
    input  logic [11:0] alignment_mask,

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]    fub_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    fub_rid,
    output logic [AXI_DATA_WIDTH-1:0]  fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [AXI_USER_WIDTH-1:0]  fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Output split information with FIFO interface
    output logic [AXI_ADDR_WIDTH-1:0]  fub_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready,

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AXI_ADDR_WIDTH-1:0]  fub_error_addr,     // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id,       // ID associated with error
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

    // Internal ready signals
    logic int_arready;
    logic int_rready;

    // OR all user-side valid signals
    assign user_valid = fub_arvalid || fub_split_valid || fub_error_valid;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_arvalid || m_axi_rvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_arready = o_cg_gating ? 1'b0 : int_arready;
    assign m_axi_rready = o_cg_gating ? 1'b0 : int_rready;

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

    // Instantiate the original AXI master read module with gated clock
    axi_master_rd #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH),
        .ERROR_FIFO_DEPTH     (ERROR_FIFO_DEPTH),
        .TIMEOUT_AR           (TIMEOUT_AR),
        .TIMEOUT_R            (TIMEOUT_R)
    ) i_axi_master_rd (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),
        .alignment_mask       (alignment_mask),

        // Slave AXI Interface (Input Side)
        .fub_arid             (fub_arid),
        .fub_araddr           (fub_araddr),
        .fub_arlen            (fub_arlen),
        .fub_arsize           (fub_arsize),
        .fub_arburst          (fub_arburst),
        .fub_arlock           (fub_arlock),
        .fub_arcache          (fub_arcache),
        .fub_arprot           (fub_arprot),
        .fub_arqos            (fub_arqos),
        .fub_arregion         (fub_arregion),
        .fub_aruser           (fub_aruser),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (int_arready),     // Connect to internal signal

        .fub_rid              (fub_rid),
        .fub_rdata            (fub_rdata),
        .fub_rresp            (fub_rresp),
        .fub_rlast            (fub_rlast),
        .fub_ruser            (fub_ruser),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),

        // Master AXI Interface (Output Side)
        .m_axi_arid           (m_axi_arid),
        .m_axi_araddr         (m_axi_araddr),
        .m_axi_arlen          (m_axi_arlen),
        .m_axi_arsize         (m_axi_arsize),
        .m_axi_arburst        (m_axi_arburst),
        .m_axi_arlock         (m_axi_arlock),
        .m_axi_arcache        (m_axi_arcache),
        .m_axi_arprot         (m_axi_arprot),
        .m_axi_arqos          (m_axi_arqos),
        .m_axi_arregion       (m_axi_arregion),
        .m_axi_aruser         (m_axi_aruser),
        .m_axi_arvalid        (m_axi_arvalid),
        .m_axi_arready        (m_axi_arready),

        .m_axi_rid            (m_axi_rid),
        .m_axi_rdata          (m_axi_rdata),
        .m_axi_rresp          (m_axi_rresp),
        .m_axi_rlast          (m_axi_rlast),
        .m_axi_ruser          (m_axi_ruser),
        .m_axi_rvalid         (m_axi_rvalid),
        .m_axi_rready         (int_rready),      // Connect to internal signal

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

endmodule : axi_master_rd_cg