// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: data_path_macro
// Purpose: "Move bytes between the host AXI buffers and the DFI data
//          lanes." Bundles wr_beat_sequencer + rd_cl_aligner.
//
// Boundaries:
//          * Host-AXI side  → consumes the axi_frontend's w_buf
//                             (beat_pull_*, wbuf_rd_data/strb), drives
//                             b_complete back to wr CAM, rd_inject + rd_beat
//                             back to the rd CAM and intake R-FSM.
//          * Scheduler side → op handshakes (wr_op_*, rd_op_*) + live
//                             MR values (cl/cwl/al).
//          * DFI side       → drives pre-pack dfi_wrdata/en/mask and
//                             dfi_rddata_en into dfi_v21_interface_macro;
//                             receives dfi_rddata + dfi_rddata_valid.
//
// Status:  SKELETON wrapper.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module data_path_macro
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ID_WIDTH    = 4,
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int W_BUF_PTR_WIDTH = 7,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_RATE        = 2,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DRAM_STRB_WIDTH = DRAM_BEAT_WIDTH / 8,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,
    parameter int MAX_BURST_LEN   = 256,

    parameter int IW  = AXI_ID_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ---- live MR values ----
    input  logic [3:0]                 cl_i,
    input  logic [3:0]                 cwl_i,
    input  logic [3:0]                 al_i,

    // ---- PHY timing (CSR-loaded after DFI init) ----
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,

    // ---- multi-outstanding read ordering mode (v2; tied off in v1) ----
    input  logic                       rd_in_order_i,

    // ---- write op handshake (from scheduler/top) ----
    input  logic                       wr_op_valid_i,
    output logic                       wr_op_ready_o,
    input  logic [WSL-1:0]             wr_op_slot_i,
    input  logic [BLW-1:0]             wr_op_len_i,

    // ---- read op handshake (from scheduler/top) ----
    input  logic                       rd_op_valid_i,
    output logic                       rd_op_ready_o,
    input  logic [RSL-1:0]             rd_op_slot_i,
    input  logic [IW-1:0]              rd_op_id_i,
    input  logic [BLW-1:0]             rd_op_len_i,

    // ---- host w_buf pull (axi_frontend ↔ wr_beat_sequencer) ----
    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    // wbuf read is one DRAM beat per cycle (the wr CAM beat_pull port
    // exposes a single read at a time).
    input  logic [DRAM_BEAT_WIDTH-1:0] wbuf_rd_data_i,
    input  logic [DRAM_STRB_WIDTH-1:0] wbuf_rd_strb_i,

    // ---- b_complete back to host wr CAM ----
    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o,

    // ---- rd_inject path (axi_frontend ← rd_cl_aligner). One DRAM beat
    //      per cycle to the axi_frontend R FSM. ----
    output logic                       rd_inject_valid_o,
    input  logic                       rd_inject_ready_i,
    output logic [IW-1:0]              rd_inject_id_o,
    output logic [DRAM_BEAT_WIDTH-1:0] rd_inject_data_o,
    output logic                       rd_inject_last_o,

    // ---- rd beat strobe back to host rd CAM ----
    output logic                       rd_beat_we_o,
    output logic [RSL-1:0]             rd_beat_slot_o,

    // ---- pre-pack DFI write/read data (to dfi_v21_interface_macro) ----
    output logic [DFI_DATA_WIDTH-1:0]  pre_dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    pre_dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  pre_dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    pre_dfi_rddata_en_o,

    // ---- DFI read data path (PHY → MC) ----
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i
);

    wr_beat_sequencer_fub #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .W_BUF_PTR_WIDTH (WPW),
        .BURST_LEN_WIDTH (BLW),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DRAM_STRB_WIDTH (DRAM_STRB_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH),
        .MAX_BURST_LEN   (MAX_BURST_LEN)
    ) u_wr_beat_sequencer (
        .mc_clk               (mc_clk),
        .mc_rst_n             (mc_rst_n),
        .cwl_i                (cwl_i),
        .t_phy_wrlat_i        (t_phy_wrlat_i),
        .op_valid_i           (wr_op_valid_i),
        .op_ready_o           (wr_op_ready_o),
        .op_slot_i            (wr_op_slot_i),
        .op_len_i             (wr_op_len_i),
        .beat_pull_strb_o     (beat_pull_strb_o),
        .beat_pull_slot_o     (beat_pull_slot_o),
        .beat_pull_ptr_i      (beat_pull_ptr_i),
        .beat_pull_strb_ptr_i (beat_pull_strb_ptr_i),
        .beat_pull_last_i     (beat_pull_last_i),
        .wbuf_rd_data_i       (wbuf_rd_data_i),
        .wbuf_rd_strb_i       (wbuf_rd_strb_i),
        .dfi_wrdata_o         (pre_dfi_wrdata_o),
        .dfi_wrdata_en_o      (pre_dfi_wrdata_en_o),
        .dfi_wrdata_mask_o    (pre_dfi_wrdata_mask_o),
        .b_complete_strb_o    (b_complete_strb_o),
        .b_complete_slot_o    (b_complete_slot_o)
    );

    rd_cl_aligner_fub #(
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .AXI_ID_WIDTH    (IW),
        .BURST_LEN_WIDTH (BLW),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_VALID_WIDTH (DFI_VALID_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH),
        .MAX_BURST_LEN   (MAX_BURST_LEN)
    ) u_rd_cl_aligner (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .cl_i               (cl_i),
        .al_i               (al_i),
        .t_rddata_en_i      (t_rddata_en_i),
        .rd_in_order_i      (rd_in_order_i),
        .op_valid_i         (rd_op_valid_i),
        .op_ready_o         (rd_op_ready_o),
        .op_slot_i          (rd_op_slot_i),
        .op_id_i            (rd_op_id_i),
        .op_len_i           (rd_op_len_i),
        .dfi_rddata_en_o    (pre_dfi_rddata_en_o),
        .dfi_rddata_i       (dfi_rddata_i),
        .dfi_rddata_valid_i (dfi_rddata_valid_i),
        .rd_inject_valid_o  (rd_inject_valid_o),
        .rd_inject_ready_i  (rd_inject_ready_i),
        .rd_inject_id_o     (rd_inject_id_o),
        .rd_inject_data_o   (rd_inject_data_o),
        .rd_inject_last_o   (rd_inject_last_o),
        .rd_beat_we_o       (rd_beat_we_o),
        .rd_beat_slot_o     (rd_beat_slot_o)
    );

endmodule : data_path_macro
