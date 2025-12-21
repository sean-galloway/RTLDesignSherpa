// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_rd_cg
// Purpose: AXI5 Master Read with Clock Gating support
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_rd_cg
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,
    parameter int AXI_CHUNKNUM_WIDTH = 4,

    // Feature enables
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI5 Interface (Input Side)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // AXI5 AR signals
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_arnsaid,
    input  logic                       fub_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_armecid,
    input  logic                       fub_axi_arunique,
    input  logic                       fub_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_artagop,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // AXI5 R signals
    output logic                       fub_axi_rtrace,
    output logic                       fub_axi_rpoison,
    output logic                       fub_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0] fub_axi_rchunkstrb,
    output logic [TW-1:0]              fub_axi_rtag,
    output logic                       fub_axi_rtagmatch,

    // Master AXI5 Interface (Output Side)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // AXI5 AR signals
    output logic [AXI_NSAID_WIDTH-1:0] m_axi_arnsaid,
    output logic                       m_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]  m_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0] m_axi_armecid,
    output logic                       m_axi_arunique,
    output logic                       m_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0] m_axi_artagop,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // AXI5 R signals
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

    // Clock gating status
    output logic                       cg_gating,
    output logic                       cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals from base module
    logic int_arready;
    logic int_rready;
    logic int_busy;

    // OR all user-side valid signals
    assign user_valid = fub_axi_arvalid || fub_axi_rready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_arvalid || m_axi_rvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_axi_arready = cg_gating ? 1'b0 : int_arready;
    assign m_axi_rready = cg_gating ? 1'b0 : int_rready;

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    // Instantiate the base AXI5 master read module with gated clock
    axi5_master_rd #(
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .SKID_DEPTH_AR       (SKID_DEPTH_AR),
        .SKID_DEPTH_R        (SKID_DEPTH_R),
        .AXI_NSAID_WIDTH     (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH      (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH     (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH       (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH     (AXI_TAGOP_WIDTH),
        .AXI_CHUNKNUM_WIDTH  (AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID        (ENABLE_NSAID),
        .ENABLE_TRACE        (ENABLE_TRACE),
        .ENABLE_MPAM         (ENABLE_MPAM),
        .ENABLE_MECID        (ENABLE_MECID),
        .ENABLE_UNIQUE       (ENABLE_UNIQUE),
        .ENABLE_CHUNKING     (ENABLE_CHUNKING),
        .ENABLE_MTE          (ENABLE_MTE),
        .ENABLE_POISON       (ENABLE_POISON)
    ) i_axi5_master_rd (
        .aclk                (gated_aclk),
        .aresetn             (aresetn),

        // Slave AXI5 Interface
        .fub_axi_arid        (fub_axi_arid),
        .fub_axi_araddr      (fub_axi_araddr),
        .fub_axi_arlen       (fub_axi_arlen),
        .fub_axi_arsize      (fub_axi_arsize),
        .fub_axi_arburst     (fub_axi_arburst),
        .fub_axi_arlock      (fub_axi_arlock),
        .fub_axi_arcache     (fub_axi_arcache),
        .fub_axi_arprot      (fub_axi_arprot),
        .fub_axi_arqos       (fub_axi_arqos),
        .fub_axi_aruser      (fub_axi_aruser),
        .fub_axi_arvalid     (fub_axi_arvalid),
        .fub_axi_arready     (int_arready),
        .fub_axi_arnsaid     (fub_axi_arnsaid),
        .fub_axi_artrace     (fub_axi_artrace),
        .fub_axi_armpam      (fub_axi_armpam),
        .fub_axi_armecid     (fub_axi_armecid),
        .fub_axi_arunique    (fub_axi_arunique),
        .fub_axi_archunken   (fub_axi_archunken),
        .fub_axi_artagop     (fub_axi_artagop),

        .fub_axi_rid         (fub_axi_rid),
        .fub_axi_rdata       (fub_axi_rdata),
        .fub_axi_rresp       (fub_axi_rresp),
        .fub_axi_rlast       (fub_axi_rlast),
        .fub_axi_ruser       (fub_axi_ruser),
        .fub_axi_rvalid      (fub_axi_rvalid),
        .fub_axi_rready      (fub_axi_rready),
        .fub_axi_rtrace      (fub_axi_rtrace),
        .fub_axi_rpoison     (fub_axi_rpoison),
        .fub_axi_rchunkv     (fub_axi_rchunkv),
        .fub_axi_rchunknum   (fub_axi_rchunknum),
        .fub_axi_rchunkstrb  (fub_axi_rchunkstrb),
        .fub_axi_rtag        (fub_axi_rtag),
        .fub_axi_rtagmatch   (fub_axi_rtagmatch),

        // Master AXI5 Interface
        .m_axi_arid          (m_axi_arid),
        .m_axi_araddr        (m_axi_araddr),
        .m_axi_arlen         (m_axi_arlen),
        .m_axi_arsize        (m_axi_arsize),
        .m_axi_arburst       (m_axi_arburst),
        .m_axi_arlock        (m_axi_arlock),
        .m_axi_arcache       (m_axi_arcache),
        .m_axi_arprot        (m_axi_arprot),
        .m_axi_arqos         (m_axi_arqos),
        .m_axi_aruser        (m_axi_aruser),
        .m_axi_arvalid       (m_axi_arvalid),
        .m_axi_arready       (m_axi_arready),
        .m_axi_arnsaid       (m_axi_arnsaid),
        .m_axi_artrace       (m_axi_artrace),
        .m_axi_armpam        (m_axi_armpam),
        .m_axi_armecid       (m_axi_armecid),
        .m_axi_arunique      (m_axi_arunique),
        .m_axi_archunken     (m_axi_archunken),
        .m_axi_artagop       (m_axi_artagop),

        .m_axi_rid           (m_axi_rid),
        .m_axi_rdata         (m_axi_rdata),
        .m_axi_rresp         (m_axi_rresp),
        .m_axi_rlast         (m_axi_rlast),
        .m_axi_ruser         (m_axi_ruser),
        .m_axi_rvalid        (m_axi_rvalid),
        .m_axi_rready        (int_rready),
        .m_axi_rtrace        (m_axi_rtrace),
        .m_axi_rpoison       (m_axi_rpoison),
        .m_axi_rchunkv       (m_axi_rchunkv),
        .m_axi_rchunknum     (m_axi_rchunknum),
        .m_axi_rchunkstrb    (m_axi_rchunkstrb),
        .m_axi_rtag          (m_axi_rtag),
        .m_axi_rtagmatch     (m_axi_rtagmatch),

        .busy                (int_busy)
    );

endmodule : axi5_master_rd_cg
