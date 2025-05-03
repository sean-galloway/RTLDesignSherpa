`timescale 1ns / 1ps

// Import packages
import axi_pkg::*;
import amba_error_pkg::*;

module axi_master
#(
    // Skid buffer depths
    parameter int DEPTH_AW          = 2,
    parameter int DEPTH_W           = 4,
    parameter int DEPTH_B           = 2,
    parameter int DEPTH_AR          = 2,
    parameter int DEPTH_R           = 4,
    parameter int MAX_OUTSTANDING        = 8,
    parameter int USER_DATA_WIDTH        = 32,    // User side data width

    // AXI Interface Parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int UDW      = USER_DATA_WIDTH,
    parameter int SW       = AXI_DATA_WIDTH / 8,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic                      aclk,
    input  logic                      aresetn,

    // User Write Command Interface
    input  logic                      i_user_wr_cmd_valid,
    output logic                      o_user_wr_cmd_ready,
    input  logic [AW-1:0]            i_user_wr_cmd_addr,
    input  logic [7:0]               i_user_wr_cmd_len,
    input  logic [2:0]               i_user_wr_cmd_size,
    input  logic [1:0]               i_user_wr_cmd_burst,
    input  logic [IW-1:0]            i_user_wr_cmd_id,
    input  logic                      i_user_wr_cmd_lock,
    input  logic [3:0]               i_user_wr_cmd_cache,
    input  logic [2:0]               i_user_wr_cmd_prot,
    input  logic [3:0]               i_user_wr_cmd_qos,
    input  logic [3:0]               i_user_wr_cmd_region,
    input  logic [UW-1:0]            i_user_wr_cmd_user,
    input  logic [11:0]              i_wr_alignment_boundary,

    // User Write Data Interface
    input  logic [UDW-1:0]           i_user_wdata,
    input  logic [UDW/8-1:0]         i_user_wstrb,
    input  logic                     i_user_wvalid,
    output logic                     o_user_wready,
    input  logic                     i_user_wlast,

    // User Write Response Interface
    output logic                      o_user_bvalid,
    input  logic                      i_user_bready,
    output logic [1:0]                o_user_bresp,
    output logic [IW-1:0]             o_user_bid,

    // User Read Command Interface
    input  logic                      i_user_rd_cmd_valid,
    output logic                      o_user_rd_cmd_ready,
    input  logic [AW-1:0]             i_user_rd_cmd_addr,
    input  logic [7:0]                i_user_rd_cmd_len,
    input  logic [2:0]                i_user_rd_cmd_size,
    input  logic [1:0]                i_user_rd_cmd_burst,
    input  logic [IW-1:0]             i_user_rd_cmd_id,
    input  logic                      i_user_rd_cmd_lock,
    input  logic [3:0]                i_user_rd_cmd_cache,
    input  logic [2:0]                i_user_rd_cmd_prot,
    input  logic [3:0]                i_user_rd_cmd_qos,
    input  logic [3:0]                i_user_rd_cmd_region,
    input  logic [UW-1:0]             i_user_rd_cmd_user,
    input  logic [11:0]               i_rd_alignment_boundary,

    // User Read Data Interface
    output logic [UDW-1:0]            o_user_rdata,
    output logic                      o_user_rvalid,
    input  logic                      i_user_rready,
    output logic                      o_user_rlast,

    // Write address channel (AW)
    output logic [IW-1:0]             m_axi_awid,
    output logic [AW-1:0]             m_axi_awaddr,
    output logic [7:0]                m_axi_awlen,
    output logic [2:0]                m_axi_awsize,
    output logic [1:0]                m_axi_awburst,
    output logic                      m_axi_awlock,
    output logic [3:0]                m_axi_awcache,
    output logic [2:0]                m_axi_awprot,
    output logic [3:0]                m_axi_awqos,
    output logic [3:0]                m_axi_awregion,
    output logic [UW-1:0]             m_axi_awuser,
    output logic                      m_axi_awvalid,
    input  logic                      m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]            m_axi_wdata,
    output logic [SW-1:0]            m_axi_wstrb,
    output logic                     m_axi_wlast,
    output logic [UW-1:0]            m_axi_wuser,
    output logic                     m_axi_wvalid,
    input  logic                     m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]            m_axi_bid,
    input  logic [1:0]               m_axi_bresp,
    input  logic [UW-1:0]            m_axi_buser,
    input  logic                     m_axi_bvalid,
    output logic                     m_axi_bready,

    // Read address channel (AR)
    output logic [IW-1:0]            m_axi_arid,
    output logic [AW-1:0]            m_axi_araddr,
    output logic [7:0]               m_axi_arlen,
    output logic [2:0]               m_axi_arsize,
    output logic [1:0]               m_axi_arburst,
    output logic                     m_axi_arlock,
    output logic [3:0]               m_axi_arcache,
    output logic [2:0]               m_axi_arprot,
    output logic [3:0]               m_axi_arqos,
    output logic [3:0]               m_axi_arregion,
    output logic [UW-1:0]            m_axi_aruser,
    output logic                     m_axi_arvalid,
    input  logic                     m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]            m_axi_rid,
    input  logic [DW-1:0]            m_axi_rdata,
    input  logic [1:0]               m_axi_rresp,
    input  logic                     m_axi_rlast,
    input  logic [UW-1:0]            m_axi_ruser,
    input  logic                     m_axi_rvalid,
    output logic                     m_axi_rready,

    // Error and Status Interface
    output error_type_t              o_wr_error_type,
    output logic [31:0]              o_wr_error_count,
    output logic [31:0]              o_wr_error_addr,
    output logic [31:0]              o_wr_trans_count,
    output logic [31:0]              o_wr_timeout_count,

    output error_type_t              o_rd_error_type,
    output logic [31:0]              o_rd_error_count,
    output logic [31:0]              o_rd_error_addr,
    output logic [31:0]              o_rd_trans_count,
    output logic [31:0]              o_rd_timeout_count
);

    // Instantiate write master
    axi_master_wr #(
        .DEPTH_AW       (DEPTH_AW),
        .DEPTH_W        (DEPTH_W),
        .DEPTH_B        (DEPTH_B),
        .MAX_OUTSTANDING     (MAX_OUTSTANDING),
        .USER_DATA_WIDTH     (USER_DATA_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH)
    ) u_axi_master_wr (
        .aclk                (aclk),
        .aresetn             (aresetn),

        // User Command Interface
        .i_user_cmd_valid    (i_user_wr_cmd_valid),
        .o_user_cmd_ready    (o_user_wr_cmd_ready),
        .i_user_cmd_addr     (i_user_wr_cmd_addr),
        .i_user_cmd_len      (i_user_wr_cmd_len),
        .i_user_cmd_size     (i_user_wr_cmd_size),
        .i_user_cmd_burst    (i_user_wr_cmd_burst),
        .i_user_cmd_id       (i_user_wr_cmd_id),
        .i_user_cmd_lock     (i_user_wr_cmd_lock),
        .i_user_cmd_cache    (i_user_wr_cmd_cache),
        .i_user_cmd_prot     (i_user_wr_cmd_prot),
        .i_user_cmd_qos      (i_user_wr_cmd_qos),
        .i_user_cmd_region   (i_user_wr_cmd_region),
        .i_user_cmd_user     (i_user_wr_cmd_user),
        .i_alignment_boundary (i_wr_alignment_boundary),

        // User Write Data Interface
        .i_user_wdata        (i_user_wdata),
        .i_user_wstrb        (i_user_wstrb),
        .i_user_wvalid       (i_user_wvalid),
        .o_user_wready       (o_user_wready),
        .i_user_wlast        (i_user_wlast),

        // User Write Response Interface
        .o_user_bvalid       (o_user_bvalid),
        .i_user_bready       (i_user_bready),
        .o_user_bresp        (o_user_bresp),
        .o_user_bid          (o_user_bid),

        // Write address channel (AW)
        .m_axi_awid          (m_axi_awid),
        .m_axi_awaddr        (m_axi_awaddr),
        .m_axi_awlen         (m_axi_awlen),
        .m_axi_awsize        (m_axi_awsize),
        .m_axi_awburst       (m_axi_awburst),
        .m_axi_awlock        (m_axi_awlock),
        .m_axi_awcache       (m_axi_awcache),
        .m_axi_awprot        (m_axi_awprot),
        .m_axi_awqos         (m_axi_awqos),
        .m_axi_awregion      (m_axi_awregion),
        .m_axi_awuser        (m_axi_awuser),
        .m_axi_awvalid       (m_axi_awvalid),
        .m_axi_awready       (m_axi_awready),

        // Write data channel (W)
        .m_axi_wdata         (m_axi_wdata),
        .m_axi_wstrb         (m_axi_wstrb),
        .m_axi_wlast         (m_axi_wlast),
        .m_axi_wuser         (m_axi_wuser),
        .m_axi_wvalid        (m_axi_wvalid),
        .m_axi_wready        (m_axi_wready),

        // Write response channel (B)
        .m_axi_bid           (m_axi_bid),
        .m_axi_bresp         (m_axi_bresp),
        .m_axi_buser         (m_axi_buser),
        .m_axi_bvalid        (m_axi_bvalid),
        .m_axi_bready        (m_axi_bready),

        // Error and Status Interface
        .o_error_type        (o_wr_error_type),
        .o_error_count       (o_wr_error_count),
        .o_error_addr        (o_wr_error_addr),
        .o_trans_count       (o_wr_trans_count),
        .o_timeout_count     (o_wr_timeout_count)
    );

// Instantiate read master
axi_master_rd #(
    .DEPTH_AR       (DEPTH_AR),
    .DEPTH_R        (DEPTH_R),
    .MAX_OUTSTANDING     (MAX_OUTSTANDING),
    .USER_DATA_WIDTH     (USER_DATA_WIDTH),
    .AXI_ID_WIDTH        (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH      (AXI_USER_WIDTH)
) u_axi_master_rd (
    .aclk                (aclk),
    .aresetn             (aresetn),

    // User Command Interface
    .i_user_cmd_valid    (i_user_rd_cmd_valid),
    .o_user_cmd_ready    (o_user_rd_cmd_ready),
    .i_user_cmd_addr     (i_user_rd_cmd_addr),
    .i_user_cmd_len      (i_user_rd_cmd_len),
    .i_user_cmd_size     (i_user_rd_cmd_size),
    .i_user_cmd_burst    (i_user_rd_cmd_burst),
    .i_user_cmd_id       (i_user_rd_cmd_id),
    .i_user_cmd_lock     (i_user_rd_cmd_lock),
    .i_user_cmd_cache    (i_user_rd_cmd_cache),
    .i_user_cmd_prot     (i_user_rd_cmd_prot),
    .i_user_cmd_qos      (i_user_rd_cmd_qos),
    .i_user_cmd_region   (i_user_rd_cmd_region),
    .i_user_cmd_user     (i_user_rd_cmd_user),
    .i_alignment_boundary (i_rd_alignment_boundary),

    // User Read Data Interface
    .o_user_rdata        (o_user_rdata),
    .o_user_rvalid       (o_user_rvalid),
    .i_user_rready       (i_user_rready),
    .o_user_rlast        (o_user_rlast),

    // Read address channel (AR)
    .m_axi_arid          (m_axi_arid),
    .m_axi_araddr        (m_axi_araddr),
    .m_axi_arlen         (m_axi_arlen),
    .m_axi_arsize        (m_axi_arsize),
    .m_axi_arburst       (m_axi_arburst),
    .m_axi_arlock        (m_axi_arlock),
    .m_axi_arcache       (m_axi_arcache),
    .m_axi_arprot        (m_axi_arprot),
    .m_axi_arqos         (m_axi_arqos),
    .m_axi_arregion      (m_axi_arregion),
    .m_axi_aruser        (m_axi_aruser),
    .m_axi_arvalid       (m_axi_arvalid),
    .m_axi_arready       (m_axi_arready),

    // Read data channel (R)
    .m_axi_rid           (m_axi_rid),
    .m_axi_rdata         (m_axi_rdata),
    .m_axi_rresp         (m_axi_rresp),
    .m_axi_rlast         (m_axi_rlast),
    .m_axi_ruser         (m_axi_ruser),
    .m_axi_rvalid        (m_axi_rvalid),
    .m_axi_rready        (m_axi_rready),

    // Error and Status Interface
    .o_error_type        (o_rd_error_type),
    .o_error_count       (o_rd_error_count),
    .o_error_addr        (o_rd_error_addr),
    .o_trans_count       (o_rd_trans_count),
    .o_timeout_count     (o_rd_timeout_count)
);

endmodule : axi_master
