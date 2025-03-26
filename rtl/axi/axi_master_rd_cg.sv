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
    input  logic [AXI_ID_WIDTH-1:0]    s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]  s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]    s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]  s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

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
    output logic [AXI_ADDR_WIDTH-1:0]  s_split_addr,
    output logic [AXI_ID_WIDTH-1:0]    s_split_id,
    output logic [7:0]                 s_split_cnt,
    output logic                       s_split_valid,
    input  logic                       s_split_ready,

    // Error outputs with FIFO interface
    output logic [3:0]                 s_error_type,     // Error type flags (AR timeout, R timeout, response error)
    output logic [AXI_ADDR_WIDTH-1:0]  s_error_addr,     // Address associated with error
    output logic [AXI_ID_WIDTH-1:0]    s_error_id,       // ID associated with error
    output logic                       s_error_valid,
    input  logic                       s_error_ready,

    // Clock gating status
    output logic                       o_cg_gating,         // Active gating indicator
    output logic                       o_cg_idle           // All buffers empty indicator
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // OR all user-side valid signals
    assign user_valid = s_axi_arvalid || s_split_valid || s_error_valid;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_arvalid || m_axi_rvalid;

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
        .ALIGNMENT_WIDTH      (ALIGNMENT_WIDTH),
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
        .alignment_mask   (alignment_mask),

        // Slave AXI Interface (Input Side)
        .s_axi_arid           (s_axi_arid),
        .s_axi_araddr         (s_axi_araddr),
        .s_axi_arlen          (s_axi_arlen),
        .s_axi_arsize         (s_axi_arsize),
        .s_axi_arburst        (s_axi_arburst),
        .s_axi_arlock         (s_axi_arlock),
        .s_axi_arcache        (s_axi_arcache),
        .s_axi_arprot         (s_axi_arprot),
        .s_axi_arqos          (s_axi_arqos),
        .s_axi_arregion       (s_axi_arregion),
        .s_axi_aruser         (s_axi_aruser),
        .s_axi_arvalid        (s_axi_arvalid),
        .s_axi_arready        (s_axi_arready),

        .s_axi_rid            (s_axi_rid),
        .s_axi_rdata          (s_axi_rdata),
        .s_axi_rresp          (s_axi_rresp),
        .s_axi_rlast          (s_axi_rlast),
        .s_axi_ruser          (s_axi_ruser),
        .s_axi_rvalid         (s_axi_rvalid),
        .s_axi_rready         (s_axi_rready),

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
        .m_axi_rready         (m_axi_rready),

        // Output split information with FIFO interface
        .s_split_addr         (s_split_addr),
        .s_split_id           (s_split_id),
        .s_split_cnt   (s_split_cnt),
        .s_split_valid        (s_split_valid),
        .s_split_ready        (s_split_ready),

        // Error outputs with FIFO interface
        .s_error_type         (s_error_type),
        .s_error_addr         (s_error_addr),
        .s_error_id           (s_error_id),
        .s_error_valid        (s_error_valid),
        .s_error_ready        (s_error_ready)
    );

endmodule : axi_master_rd_cg
