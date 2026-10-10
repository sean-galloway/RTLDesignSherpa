// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_dfi_layer
// Purpose: DFI 4.0 datapath assembly for andesite. Holds the single
//          controller<->PHY crossing (andesite_dfi_cdc async gaxi FIFOs) and
//          the dfi_clk-domain command path + write serializer + read aligner.
//          Presents the controller-clock command/wrdata/rddata streams on one
//          side and the DFI 4.0 pin bus on the other.
//
// Composition (TASK-016 t6):
//   * andesite_dfi_cdc     : ctl <-> dfi async FIFOs
//   * andesite_dfi_cmd_path: widened {ap,col,row,bg,bank,rank,op} -> DFI pins
//   * andesite_dfi_wr_serializer: DFI write data at t_phy_wrlat
//   * andesite_dfi_rd_aligner   : DFI read data alignment at t_rddata_en
//
// Training pins live on andesite_training_layer, NOT here. The P1 formatter's
// dfi_cke output is a DDR4 placeholder; the real CKE pin (cke_i) is registered
// onto dfi_cke_o. dfi_init_start_o is the CDC's registered init_busy_i.
//
// Single-rank design point: dfi_wrdata_cs_o and dfi_rddata_cs_o are driven
// constant zero, matching scoria's v3.1 precedent.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Author: sean galloway
// Created: 2026-10-05 (macro integration pass, TASK-016 t6)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_dfi_layer
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int NUM_BG          = 4,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int ADDR_WIDTH      = 18,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,

    parameter int CMD_FIFO_DEPTH  = 8,
    parameter int WD_FIFO_DEPTH   = 16,
    parameter int RD_FIFO_DEPTH   = 32,
    parameter int RD_MAX_OUTSTANDING = 16,
    parameter int RD_EN_CYC       = 4,
    parameter int BL_WORDS        = RD_EN_CYC,

    parameter int N_FLOP_CROSS    = 2,
    parameter int USE_JOHNSON     = 0,

    // ---- derived DFI geometry ----
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int BANK_WIDTH      = $clog2(NUM_BANKS),
    parameter int BG_WIDTH        = 2,
    parameter int RKW             = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW             = $clog2(NUM_BANKS),
    parameter int BGW             = (NUM_BG > 1) ? $clog2(NUM_BG) : 1,
    parameter int PHW             = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,

    // ---- FIFO payloads ----
    parameter int CMD_DW = $bits(dram_op_e) + RKW + BKW + BGW
                         + ROW_WIDTH + COL_WIDTH + 1,
    parameter int WD_DW  = 1 + DFI_STRB_WIDTH + DFI_STRB_WIDTH + DFI_DATA_WIDTH,
                                               // {last,strb,dbi,data}
    parameter int RD_DW  = 1 + 2 + DFI_STRB_WIDTH + DFI_DATA_WIDTH
                                               // {last,resp,dbi,data}
) (
    //=========================================================================
    // Controller domain (ctl_clk)
    //=========================================================================
    input  logic                       ctl_clk,
    input  logic                       ctl_rstn,

    // command stream (widened scheduler word)
    input  logic                       cmd_valid_i,
    output logic                       cmd_ready_o,
    input  logic [CMD_DW-1:0]          cmd_data_i,

    // write-data stream (DFI-word granular)
    input  logic                       wd_valid_i,
    output logic                       wd_ready_o,
    input  logic [DFI_DATA_WIDTH-1:0]  wd_data_i,
    input  logic [DFI_STRB_WIDTH-1:0]  wd_strb_i,
    input  logic [DFI_STRB_WIDTH-1:0]  wd_dbi_i,
    input  logic                       wd_last_i,

    // read-data stream (DFI-word granular; dbi travels aligned with the data)
    output logic                       rd_valid_o,
    input  logic                       rd_ready_i,
    output logic [DFI_DATA_WIDTH-1:0]  rd_data_o,
    output logic [DFI_STRB_WIDTH-1:0]  rd_dbi_o,
    output logic [1:0]                 rd_resp_o,
    output logic                       rd_last_o,

    // init status from the macro
    input  logic                       init_busy_i,
    input  logic                       init_done_i,

    // policy from the macro mode-register outputs
    input  logic                       rd_dbi_en_i,
    input  logic                       wr_dbi_en_i,

    // runtime configuration
    input  memtype_e                   memtype_i,
    input  logic                       parity_en_i,
    input  logic [1:0]                 gear_i,
    input  logic [PHW-1:0]             rd_phase_i,
    input  logic [PHW-1:0]             wr_phase_i,
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,

    // real CKE pin from the P1 init sequencer
    input  logic                       cke_i,

    //=========================================================================
    // PHY DFI domain (dfi_clk)
    //=========================================================================
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,

    // DFI 4.0 command surface
    output logic [ADDR_WIDTH-1:0]      dfi_address_o,
    output logic [BANK_WIDTH-1:0]      dfi_bank_o,
    output logic [BG_WIDTH-1:0]        dfi_bg_o,
    output logic                       dfi_act_n_o,
    output logic                       dfi_ras_n_o,
    output logic                       dfi_cas_n_o,
    output logic                       dfi_we_n_o,
    output logic [NUM_RANKS-1:0]       dfi_cs_o,
    output logic                       dfi_cke_o,
    output logic                       dfi_parity_in_o,

    // DFI write data
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [NUM_RANKS-1:0]       dfi_wrdata_cs_o,

    // DFI read data
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    input  logic [DFI_STRB_WIDTH-1:0]  dfi_rddata_dbi_i,
    output logic [NUM_RANKS-1:0]       dfi_rddata_cs_o,

    // DFI init
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    // ---- CDC dfi-side nets ----
    logic               pcmd_valid, pcmd_ready;
    logic [CMD_DW-1:0]  pcmd_data;
    logic               pwd_valid,  pwd_ready;
    logic [WD_DW-1:0]   pwd_data;
    logic               pwr_staged, pwr_staged_pop;
    logic               prd_valid,  prd_ready;
    logic [RD_DW-1:0]   prd_data;
    logic               pinit_start;
    logic               w_init_complete_unused;

    // ---- fire strobes ----
    logic               w_wr_fire, w_rd_fire, w_rd_op_ready;
    logic [RKW-1:0]     w_fire_rank;

    // ---- command-path placeholder CKE (not forwarded) ----
    logic               w_cmd_cke;

    // ---- active-gear phase mask ------------------------------------------
    localparam int RATEW = $clog2(DFI_RATE) + 1;
    logic [RATEW-1:0]        w_active_rate;
    logic [DFI_EN_WIDTH-1:0] w_phase_active;
    logic [DFI_EN_WIDTH-1:0] w_dfi_wrdata_en, w_dfi_rddata_en;

    assign w_active_rate = (RATEW'(1) << gear_i);

    always_comb begin
        for (int p = 0; p < DFI_EN_WIDTH; p++)
            w_phase_active[p] = (RATEW'(p) < w_active_rate);
    end

    assign dfi_wrdata_en_o = w_dfi_wrdata_en & w_phase_active;
    assign dfi_rddata_en_o = w_dfi_rddata_en & w_phase_active;

    // ---- pack/unpack controller-side payloads ----------------------------
    logic [WD_DW-1:0]          w_wd_packed;
    logic                      w_wd_last;
    logic [DFI_STRB_WIDTH-1:0] w_wd_strb, w_wd_dbi;
    logic [DFI_DATA_WIDTH-1:0] w_wd_data;

    assign w_wd_packed = {wd_last_i, wd_strb_i, wd_dbi_i, wd_data_i};
    assign {w_wd_last, w_wd_strb, w_wd_dbi, w_wd_data} = pwd_data;

    logic                      w_rd_last;
    logic [1:0]                w_rd_resp;
    logic [DFI_STRB_WIDTH-1:0] w_rd_dbi;
    logic [DFI_DATA_WIDTH-1:0] w_rd_data;
    assign prd_data = {w_rd_last, w_rd_resp, w_rd_dbi, w_rd_data};

    // Controller-side read return: unpack the packed CDC word (last/resp/db i/data).
    logic [RD_DW-1:0]          w_rd_packed;

    assign {rd_last_o, rd_resp_o, rd_dbi_o, rd_data_o} = w_rd_packed;

    // ======================================================================
    // Single CDC (async gaxi FIFOs)
    // ======================================================================
    andesite_dfi_cdc #(
        .CMD_DW      (CMD_DW),
        .WD_DW       (WD_DW),
        .RD_DW       (RD_DW),
        .CMD_DEPTH   (CMD_FIFO_DEPTH),
        .WD_DEPTH    (WD_FIFO_DEPTH),
        .RD_DEPTH    (RD_FIFO_DEPTH),
        .N_FLOP_CROSS(N_FLOP_CROSS),
        .USE_JOHNSON (USE_JOHNSON)
    ) u_cdc (
        .ctl_clk         (ctl_clk),
        .ctl_rstn        (ctl_rstn),
        .cmd_valid_i     (cmd_valid_i),
        .cmd_ready_o     (cmd_ready_o),
        .cmd_data_i      (cmd_data_i),
        .wd_valid_i      (wd_valid_i),
        .wd_ready_o      (wd_ready_o),
        .wd_data_i       (w_wd_packed),
        .wd_last_i       (wd_last_i),
        .init_start_i    (init_busy_i),
        .rd_valid_o      (rd_valid_o),
        .rd_ready_i      (rd_ready_i),
        .rd_data_o       (w_rd_packed),
        .init_complete_o (w_init_complete_unused),
        .dfi_clk         (dfi_clk),
        .dfi_rstn        (dfi_rstn),
        .pcmd_valid_o    (pcmd_valid),
        .pcmd_ready_i    (pcmd_ready),
        .pcmd_data_o     (pcmd_data),
        .pwd_valid_o     (pwd_valid),
        .pwd_ready_i     (pwd_ready),
        .pwd_data_o      (pwd_data),
        .pwr_staged_valid_o(pwr_staged),
        .pwr_staged_pop_i(pwr_staged_pop),
        .pinit_start_o   (pinit_start),
        .prd_valid_i     (prd_valid),
        .prd_ready_o     (prd_ready),
        .prd_data_i      (prd_data),
        .pinit_complete_i(dfi_init_complete_i)
    );

    assign dfi_init_start_o = pinit_start;

    // ======================================================================
    // Command path (dfi_clk): cmd FIFO -> DFI command bus + fire strobes
    // ======================================================================
    andesite_dfi_cmd_path #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS),
        .NUM_BG    (NUM_BG),
        .ROW_WIDTH (ROW_WIDTH),
        .COL_WIDTH (COL_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_cmd_path (
        .dfi_clk        (dfi_clk),
        .dfi_rstn       (dfi_rstn),
        .memtype_i      (memtype_i),
        .parity_en_i    (parity_en_i),
        .cmd_valid_i    (pcmd_valid),
        .cmd_ready_o    (pcmd_ready),
        .cmd_data_i     (pcmd_data),
        .rd_op_ready_i  (w_rd_op_ready),
        .wr_op_ready_i  (pwr_staged),
        .wr_fire_o      (w_wr_fire),
        .rd_fire_o      (w_rd_fire),
        .fire_rank_o    (w_fire_rank),
        .wr_accept_o    (pwr_staged_pop),
        .dfi_address_o  (dfi_address_o),
        .dfi_bank_o     (dfi_bank_o),
        .dfi_bg_o       (dfi_bg_o),
        .dfi_act_n_o    (dfi_act_n_o),
        .dfi_ras_n_o    (dfi_ras_n_o),
        .dfi_cas_n_o    (dfi_cas_n_o),
        .dfi_we_n_o     (dfi_we_n_o),
        .dfi_cs_o       (dfi_cs_o),
        .dfi_cke_o      (w_cmd_cke),
        .dfi_parity_in_o(dfi_parity_in_o)
    );

    // ======================================================================
    // Write serializer (dfi_clk): wrdata FIFO -> dfi_wrdata at t_phy_wrlat
    // ======================================================================
    andesite_dfi_wr_serializer #(
        .DFI_DATA_WIDTH(DFI_DATA_WIDTH),
        .DFI_RATE      (DFI_RATE)
    ) u_wr (
        .dfi_clk          (dfi_clk),
        .dfi_rstn         (dfi_rstn),
        .t_phy_wrlat_i    (t_phy_wrlat_i),
        .wr_fire_i        (w_wr_fire),
        .wd_valid_i       (pwd_valid),
        .wd_ready_o       (pwd_ready),
        .wd_data_i        (w_wd_data),
        .wd_strb_i        (w_wd_strb),
        .wd_last_i        (w_wd_last),
        .db_wr_dbi_en_i   (wr_dbi_en_i),
        .wd_dbi_i         (w_wd_dbi),
        .dfi_wrdata_o     (dfi_wrdata_o),
        .dfi_wrdata_en_o  (w_dfi_wrdata_en),
        .dfi_wrdata_mask_o(dfi_wrdata_mask_o)
    );

    // ======================================================================
    // Read aligner (dfi_clk): dfi_rddata -> rddata FIFO at t_rddata_en
    // ======================================================================
    andesite_dfi_rd_aligner #(
        .DFI_DATA_WIDTH (DFI_DATA_WIDTH),
        .DFI_RATE       (DFI_RATE),
        .BL_WORDS       (BL_WORDS),
        .EN_CYC         (RD_EN_CYC),
        .MAX_OUTSTANDING(RD_MAX_OUTSTANDING)
    ) u_rd (
        .dfi_clk           (dfi_clk),
        .dfi_rstn          (dfi_rstn),
        .t_rddata_en_i     (t_rddata_en_i),
        .op_valid_i        (w_rd_fire),
        .op_ready_o        (w_rd_op_ready),
        .dfi_rddata_en_o   (w_dfi_rddata_en),
        .dfi_rddata_i      (dfi_rddata_i),
        .dfi_rddata_valid_i(dfi_rddata_valid_i),
        .rd_valid_o        (prd_valid),
        .rd_ready_i        (prd_ready),
        .rd_data_o         (w_rd_data),
        .rd_resp_o         (w_rd_resp),
        .rd_last_o         (w_rd_last),
        .rd_dbi_en_i       (rd_dbi_en_i),
        .dfi_rddata_dbi_i  (dfi_rddata_dbi_i),
        .rd_dbi_o          (w_rd_dbi)
    );

    // ======================================================================
    // Single-rank CS-qualified data lanes (scoria v3.1 precedent)
    // ======================================================================
    assign dfi_wrdata_cs_o = '0;
    assign dfi_rddata_cs_o = '0;

    // ======================================================================
    // CKE and init start: register the controller-side CKE onto dfi_clk.
    // The P1 formatter's dfi_cke is a placeholder and is intentionally not
    // forwarded.
    // ======================================================================
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            dfi_cke_o <= 1'b0;
        end else begin
            dfi_cke_o <= cke_i;
        end
    )

    // ---- silence unused/placeholder warnings ----
    wire unused = &{1'b0, w_fire_rank, init_done_i, rd_phase_i, wr_phase_i,
                    w_cmd_cke, w_init_complete_unused, 1'b0};

endmodule : andesite_dfi_layer
