// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_core
// Purpose: The andesite DDR4/LPDDR4 controller core. Wires the four macro
//          layers built bottom-up this cycle:
//            1. mc_axi4_layer      (host AXI + wr/rd CAMs)
//            2. andesite_scheduler_layer (bank timers + arbiter + refresh/init)
//            3. andesite_training_layer  (DFI training pins + maintenance cmds)
//            4. andesite_dfi_layer       (async CDC + DFI 4.0 datapath)
//
//          Host AXI + scheduler + CAMs run on aclk; the DFI phase-packer + PHY
//          run on dfi_clk; the clock crossings live in andesite_dfi_layer's
//          CDC and andesite_training_layer's training-pin synchronizers.
//          Internal data unit = the DFI word (DFI_DATA_WIDTH); the host AXI
//          data width is the DFI word too (an external dwidth shim is a
//          separate edge concern).
//
//          Config (timings / phases / policy) is delivered on ports here; a
//          by-name CSR register block is a clean-rebuild follow-up.
//
// Documentation: docs/uarch/ANDESITE_DFI_LAYER_UARCH.md (+ the HAS / scheduler specs)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_core
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int NUM_RANKS      = 1,
    parameter int NUM_CS         = NUM_RANKS,
    parameter int NUM_BANKS      = 8,
    parameter int NUM_BG         = 4,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int ADDR_WIDTH     = 18,
    parameter int DFI_RATE       = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int DRAM_BL        = 8,
    parameter int NUM_ENTRIES    = 8,
    parameter int N_SRAM_SLOTS   = NUM_ENTRIES,
    parameter int RD_RET_DEPTH   = 32,
    parameter int CMD_DELAY      = 0,
    parameter int AGE_WIDTH      = 16,
    parameter int CMD_HISTORY_EN = 0,
    parameter int HIST_T_RFC_CORE = 0,
    parameter int HIST_T_RTW_CORE = 0,
    parameter int HIST_T_WTR_CORE = 0,

    parameter int BYTE_OFFSET_WIDTH = $clog2(DRAM_DEVICE_WIDTH / 8),
    parameter int BL_SHIFT   = (DRAM_BEAT_WIDTH > DRAM_DEVICE_WIDTH)
                             ? $clog2(DRAM_BEAT_WIDTH / DRAM_DEVICE_WIDTH) : 0,
    parameter int BL_PUMICE  = DRAM_BL >> BL_SHIFT,
    parameter int BURST_WORDS = (BL_PUMICE >= DFI_RATE) ? (BL_PUMICE / DFI_RATE) : 1,
    parameter int N_SUBCMD    = (DFI_RATE > BL_PUMICE) ? (DFI_RATE / BL_PUMICE) : 1,
    parameter int SUB_COL_STRIDE = DRAM_BL,
    parameter int SUB_PHASE_STRIDE = (N_SUBCMD > 1) ? (DFI_RATE / N_SUBCMD) : 1,
    parameter int RD_EN_CYC_CORE = (DRAM_BL + DFI_RATE - 1) / DFI_RATE,

    parameter int DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DW  = DFI_DATA_WIDTH,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int UW  = 1,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int BGW = (NUM_BG > 1) ? $clog2(NUM_BG) : 1,
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int N_LU = NUM_BANKS,
    parameter int DFI_STRB_WIDTH  = DW / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_CS_BUS_W    = NUM_RANKS * DFI_RATE
) (
    // ---- controller clock (host AXI + scheduler + CAMs) ----
    input  logic                       aclk,
    input  logic                       aresetn,
    // ---- DFI/PHY clock ----
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,

    // ---- config (ports; CSR rebuild is a follow-up) ----
    input  memtype_e                   memtype_i,
    input  page_policy_e               page_policy_i,

    // ---- runtime page-policy CSR fields + telemetry ----
    input  logic [2:0]                 page_mode_i,
    input  logic [7:0]                 page_tr_init_i,
    input  logic [1:0]                 sched_order_mode_i,
    input  logic [1:0]                 sched_row_sel_i,
    input  logic [1:0]                 sched_col_sel_i,
    input  logic [1:0]                 sched_access_pref_i,
    input  logic [7:0]                 sched_wr_high_wm_i,
    input  logic [7:0]                 sched_wr_batch_max_i,
    input  logic [7:0]                 sched_wr_low_wm_i,
    input  logic [1:0]                 sched_prio_sub_i,
    input  logic                       sched_qos_en_i,
    input  logic [7:0]                 sched_age_thresh_i,

    // stall-cause attribution
    output logic [31:0]                stall_bp_o,
    output logic [31:0]                stall_refresh_o,
    output logic [31:0]                stall_turnaround_o,
    output logic [31:0]                stall_tccd_o,
    output logic [31:0]                stall_actlimit_o,
    output logic [31:0]                stall_banktimer_o,
    output logic [31:0]                stall_noreq_o,
    output logic [31:0]                stall_zq_o,
    output logic [31:0]                stat_page_hit_o,
    output logic [31:0]                stat_row_hit_o [NUM_BANKS],
    output logic [31:0]                stat_page_miss_o,
    output logic [31:0]                stat_page_empty_o,
    output logic [31:0]                stat_act_o,
    output logic [31:0]                stat_pre_o,
    output logic [31:0]                stat_ref_o,
    output logic [31:0]                stat_ref_busy_o,

    input  logic [4:0]                 bank_lsb_i,
    input  logic                       hash_en_i,
    input  logic [7:0]                 hash_seed_i,
    input  logic [7:0]                 t_rcd_i, t_rp_i, t_ras_i, t_rc_i, t_wr_i, t_rtp_i,
    input  logic [7:0]                 t_faw_i, t_rrd_i, t_wtr_i, t_rtw_i, t_ccd_i,
    // ANDESITE L/S DELTA
    input  logic [7:0]                 t_ccd_l_i,
    input  logic [7:0]                 t_ccd_s_i,
    input  logic [7:0]                 t_rrd_l_i,
    input  logic [7:0]                 t_rrd_s_i,
    input  logic [15:0]                t_refi_i,
    input  logic                       refi_reload_i,
    input  logic [15:0]                t_rfc_i,
    // ANDESITE FGR DELTA
    input  logic [1:0]                 fgr_factor_i,
    input  logic [15:0]                t_rfc_2x_i,
    input  logic [15:0]                t_rfc_4x_i,
    input  logic [3:0]                 refresh_burst_i,
    input  logic [3:0]                 ref_postpone_i,
    input  logic [3:0]                 ref_pullin_i,
    input  logic [1:0]                 ref_mode_i,
    input  logic [15:0]                ref_trefi_pb_i,
    input  logic [7:0]                 ref_trfc_pb_i,
    // init timing
    input  logic [15:0]                t_init_wait_i, t_dll_wait_i,
    input  logic [7:0]                 t_mrd_wait_i, t_rp_wait_i,
    input  logic [15:0]                t_cke_wait_i,
    input  logic [15:0]                t_mod_wait_i,
    input  logic [15:0]                t_zqinit_wait_i,
    output logic                       dfi_reset_n_o,

    // ----- ZQ calibration ----
    input  logic                       zq_enable_i,
    input  logic [31:0]                zq_interval_i,
    input  logic [15:0]                t_zqcs_i,
    // ANDESITE MPC DELTA
    input  logic [15:0]                t_zq_i,
    input  logic [5:0]                 zq_mpc_opcode_i,
    output logic                       zq_busy_o,
    output logic [15:0]                zq_total_o,
    output logic [31:0]                zq_interval_cnt_o,
    output logic                       zq_overdue_o,

    // ----- Mode A/B/C CSR fields ----
    input  logic                       ref_elastic_en_i,
    input  logic [7:0]                 ref_pullin_idle_streak_i,
    input  logic [6:0]                 ref_postpone_demand_streak_i,
    input  logic                       ref_tcr_en_i,
    input  logic [1:0]                 ref_trefi_derate_i,
    input  logic [1:0]                 zq_placement_i,
    input  logic [12:0]                zq_overdue_max_i,
    output logic [15:0]                obs_ref_postpone_events_o,
    output logic [15:0]                obs_ref_pullin_events_o,

    // ----- write leveling ----
    input  logic                       wrlvl_strobe_i,
    input  logic [3:0]                 wrlvl_cs_sel_i,
    input  logic [15:0]                t_wldqsen_i,
    input  logic [15:0]                t_wlmrd_i,
    input  logic [15:0]                t_wlmrd_max_i,
    input  logic [15:0]                t_wlo_i,
    input  logic [15:0]                t_wloe_i,
    input  logic                       dfi_prime_dq_i,
    input  logic [NUM_CS-1:0]          dfi_phylvl_ack_cs_n_i,
    output logic [NUM_CS-1:0]          dfi_phylvl_req_cs_n_o,
    output logic [NUM_CS-1:0]          dfi_phy_wrlvl_cs_n_o,
    output logic                       dfi_wrlvl_strobe_o,

    // ----- read leveling ----
    input  logic                       rdlvl_en_i,
    input  logic [3:0]                 rdlvl_cs_sel_i,
    input  logic [15:0]                csr_mr3_mpr_enter_i,
    input  logic [15:0]                csr_mr3_mpr_exit_i,
    input  logic [15:0]                t_mpr_enter_i,
    input  logic [15:0]                t_mpr_exit_i,
    input  logic [15:0]                t_mpr_readout_i,
    input  logic [15:0]                tmod_i,
    input  logic [15:0]                t_rdlvl_timeout_i,
    input  logic                       mpr_pattern_i,
    input  logic [NUM_CS-1:0]          dfi_phylvl_req_cs_n_i,
    output logic [NUM_CS-1:0]          dfi_phylvl_ack_cs_n_o,
    output logic [NUM_CS-1:0]          dfi_phy_rdlvl_cs_n_o,

    // ----- CA/WDQ training ----
    input  logic                       ca_train_en_i,
    input  logic                       wdq_cal_en_i,
    input  logic                       chan_sel_i,
    input  logic [15:0]                csr_mpc_ca_enter_i,
    input  logic [15:0]                csr_mpc_ca_exit_i,
    input  logic [15:0]                csr_mpc_wdq_enter_i,
    input  logic [15:0]                csr_mpc_wdq_exit_i,
    input  logic [15:0]                t_ca_train_i,
    input  logic [15:0]                t_wdq_cal_i,
    input  logic [15:0]                t_ca_timeout_i,
    input  logic                       ca_sample_i,
    input  logic                       wdq_sample_i,

    // ----- mode-register CSR images ----
    input  logic [15:0]                mr0_i, mr1_i, mr2_i, mr3_i,
    input  logic [15:0]                mr4_i, mr5_i, mr6_i,
    input  logic                       init_restart_i,

    // ----- PHY/DFI runtime placement ----
    input  logic [PHW-1:0]             rd_phase_i,
    input  logic [PHW-1:0]             wr_phase_i,
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,
    input  logic [1:0]                 gear_i,
    input  logic [3:0]                 bl_i,

    // ----- init status ----
    output logic                       init_done_o,
    output logic                       init_err_o,

    // ----- policy outputs from mode register ----
    output logic [2:0]                 rtt_nom_o,
    output logic [2:0]                 rtt_wr_o,
    output logic [2:0]                 rtt_park_o,
    output logic                       rd_dbi_en_o,
    output logic                       wr_dbi_en_o,
    output logic                       parity_enable_o,

    // ---- host AXI4 (data width = DFI word) ----
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic [UW-1:0]  s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [DW-1:0]  s_axi_wdata,  input logic [SW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic [UW-1:0] s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic [UW-1:0]  s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic [UW-1:0]  s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic [UW-1:0]  s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready,

    // ---- DFI 4.0 pin bus (to PHY) ----
    output logic [ADDR_WIDTH-1:0]      dfi_address_o,
    output logic [BKW-1:0]             dfi_bank_o,
    output logic [BGW-1:0]             dfi_bg_o,
    output logic                       dfi_act_n_o,
    output logic                       dfi_ras_n_o,
    output logic                       dfi_cas_n_o,
    output logic                       dfi_we_n_o,
    output logic [NUM_RANKS-1:0]       dfi_cs_o,
    output logic                       dfi_cke_o,
    output logic                       dfi_parity_in_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [NUM_RANKS-1:0]       dfi_wrdata_cs_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    input  logic [DFI_STRB_WIDTH-1:0]  dfi_rddata_dbi_i,
    output logic [NUM_RANKS-1:0]       dfi_rddata_cs_o,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    localparam int PTRW = $clog2(NUM_ENTRIES);
    localparam int CMD_DW = $bits(dram_op_e) + RKW + BKW + BGW + ROW_WIDTH + COL_WIDTH + 1;
    localparam int WD_DW  = 1 + DFI_STRB_WIDTH + DFI_STRB_WIDTH + DFI_DATA_WIDTH;
    localparam int RD_DW  = 1 + 2 + DFI_STRB_WIDTH + DFI_DATA_WIDTH;

    // ---- runtime sub-DFI-word framing ----
    localparam int SUBW_MAX = $clog2(N_SUBCMD + 1);
    localparam int CMD_DELAY_EFF = (CMD_DELAY == 0) ? (5 + 2 * BURST_WORDS) : CMD_DELAY;
    logic [7:0] w_t_ccd_eff;
    assign w_t_ccd_eff = (t_ccd_i < 8'(BURST_WORDS)) ? 8'(BURST_WORDS) : t_ccd_i;
    logic [3:0]          w_bl_pumice;
    logic [4:0]          w_active_rate;
    logic [SUBW_MAX-1:0] w_n_subcmd;
    logic [COL_WIDTH-1:0] w_sub_col_stride;
    logic [PHW-1:0]      w_sub_phase_stride;
    always_comb begin
        w_bl_pumice   = bl_i >> BL_SHIFT;
        w_active_rate = 5'(1) << gear_i;
        if ((w_bl_pumice != '0) && (w_active_rate > 5'(w_bl_pumice)))
            w_n_subcmd = SUBW_MAX'(w_active_rate / 5'(w_bl_pumice));
        else
            w_n_subcmd = SUBW_MAX'(1);
        w_sub_col_stride = COL_WIDTH'(bl_i);
        w_sub_phase_stride = PHW'(w_bl_pumice);
    end

    // ---- scheduler <-> IFC CAM per-entry vectors ----
    logic [NUM_ENTRIES-1:0]             w_wr_sch_v,     w_rd_sch_v;
    logic [NUM_ENTRIES*BKW-1:0]         w_wr_sch_bank,  w_rd_sch_bank;
    logic [NUM_ENTRIES*ROW_WIDTH-1:0]   w_wr_sch_row,   w_rd_sch_row;
    logic [NUM_ENTRIES*COL_WIDTH-1:0]   w_wr_sch_col,   w_rd_sch_col;
    logic [NUM_ENTRIES*NUM_ENTRIES-1:0] w_wr_sch_older, w_rd_sch_older;
    logic [NUM_ENTRIES-1:0]             w_wr_sch_agex,  w_rd_sch_agex;
    logic [NUM_ENTRIES*4-1:0]           w_wr_sch_qos,   w_rd_sch_qos;
    logic [15:0]                        w_wr_sch_hrel,  w_rd_sch_hrel;
    logic                      w_wr_commit_v, w_wr_commit_rdy;
    logic [PTRW-1:0]           w_wr_commit_slot;
    logic                      w_rd_issue_v, w_rd_issue_rdy;
    logic [PTRW-1:0]           w_rd_issue_slot;

    // ---- IFC wr commit-data -> DFI wrdata ; DFI rddata -> IFC rd return ----
    logic                      w_cm_v, w_cm_rdy, w_cm_last;
    logic [DW-1:0]             w_cm_data;
    logic [SW-1:0]             w_cm_strb;
    logic                      w_ret_v, w_ret_rdy, w_ret_last;
    logic [DW-1:0]             w_ret_data;
    logic [1:0]                w_ret_resp;

    // ---- scheduler cmd stream -> DFI cmd (packed) ----
    logic                      w_cmd_v, w_cmd_rdy;
    dram_op_e                  w_cmd_op;
    logic [RKW-1:0]            w_cmd_rank;
    logic [BKW-1:0]            w_cmd_bank;
    logic [BGW-1:0]            w_cmd_bg;
    logic [ROW_WIDTH-1:0]      w_cmd_row;
    logic [COL_WIDTH-1:0]      w_cmd_col;
    logic                      w_cmd_ap;
    logic [CMD_DW-1:0]         w_cmd_data;
    assign w_cmd_data = {w_cmd_ap, w_cmd_col, w_cmd_row, w_cmd_bg, w_cmd_bank, w_cmd_rank, w_cmd_op};

    // ---- init/status/policy wiring ----
    logic                      w_init_busy;
    logic                      w_cke;
    logic                      w_rd_dbi_en, w_wr_dbi_en;
    logic                      w_wrlvl_en;
    logic [2:0]                w_rtt_nom, w_rtt_wr, w_rtt_park;
    logic                      w_parity_enable;
    logic                      dram_reset_n_o;

    assign w_init_busy = ~init_done_o;
    assign dfi_reset_n_o = dram_reset_n_o;

    // ======================================================================
    // Layer 1: AXI interface + CAMs
    // ======================================================================
    mc_axi4_layer #(
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH  (DW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        // ANDESITE BG DELTA: DDR4 bank-group intake mapping
        .BG_WIDTH        (2),
        .HAS_BG          (1),
        .AXI_BEATS_PER_BURST   (BURST_WORDS),
        .NUM_ENTRIES      (NUM_ENTRIES),
        .N_SRAM_SLOTS     (N_SRAM_SLOTS),
        .RD_RET_DEPTH     (RD_RET_DEPTH),
        .N_SCHED_LU       (N_LU),
        .AGE_WIDTH        (AGE_WIDTH)
    ) u_ifc (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .bank_lsb_i    (bank_lsb_i),
        .hash_en_i     (hash_en_i),
        .hash_seed_i   (hash_seed_i),
        .s_axi_awid    (s_axi_awid),
        .s_axi_awaddr  (s_axi_awaddr),
        .s_axi_awlen   (s_axi_awlen),
        .s_axi_awsize  (s_axi_awsize),
        .s_axi_awburst (s_axi_awburst),
        .s_axi_awlock  (s_axi_awlock),
        .s_axi_awcache (s_axi_awcache),
        .s_axi_awprot  (s_axi_awprot),
        .s_axi_awqos   (s_axi_awqos),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awuser  (s_axi_awuser),
        .s_axi_awvalid (s_axi_awvalid),
        .s_axi_awready (s_axi_awready),
        .s_axi_wdata   (s_axi_wdata),
        .s_axi_wstrb   (s_axi_wstrb),
        .s_axi_wlast   (s_axi_wlast),
        .s_axi_wuser   (s_axi_wuser),
        .s_axi_wvalid  (s_axi_wvalid),
        .s_axi_wready  (s_axi_wready),
        .s_axi_bid     (s_axi_bid),
        .s_axi_bresp   (s_axi_bresp),
        .s_axi_buser   (s_axi_buser),
        .s_axi_bvalid  (s_axi_bvalid),
        .s_axi_bready  (s_axi_bready),
        .s_axi_arid    (s_axi_arid),
        .s_axi_araddr  (s_axi_araddr),
        .s_axi_arlen   (s_axi_arlen),
        .s_axi_arsize  (s_axi_arsize),
        .s_axi_arburst (s_axi_arburst),
        .s_axi_arlock  (s_axi_arlock),
        .s_axi_arcache (s_axi_arcache),
        .s_axi_arprot  (s_axi_arprot),
        .s_axi_arqos   (s_axi_arqos),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_aruser  (s_axi_aruser),
        .s_axi_arvalid (s_axi_arvalid),
        .s_axi_arready (s_axi_arready),
        .s_axi_rid     (s_axi_rid),
        .s_axi_rdata   (s_axi_rdata),
        .s_axi_rresp   (s_axi_rresp),
        .s_axi_rlast   (s_axi_rlast),
        .s_axi_ruser   (s_axi_ruser),
        .s_axi_rvalid  (s_axi_rvalid),
        .s_axi_rready  (s_axi_rready),
        .wr_sch_valid_o     (w_wr_sch_v),
        .wr_sch_bank_o      (w_wr_sch_bank),
        .wr_sch_row_o       (w_wr_sch_row),
        .wr_sch_col_o       (w_wr_sch_col),
        .wr_sch_older_o     (w_wr_sch_older),
        .wr_sch_age_exceed_o(w_wr_sch_agex),
        .wr_sch_head_rel_o  (w_wr_sch_hrel),
        .wr_sch_qos_o       (w_wr_sch_qos),
        .rd_sch_qos_o       (w_rd_sch_qos),
        .rd_sch_age_exceed_o(w_rd_sch_agex),
        .rd_sch_head_rel_o  (w_rd_sch_hrel),
        .sched_age_thresh_i (sched_age_thresh_i),
        .wr_commit_valid_i  (w_wr_commit_v),
        .wr_commit_ready_o  (w_wr_commit_rdy),
        .wr_commit_slot_i   (w_wr_commit_slot),
        .wr_cm_rd_valid_o   (w_cm_v),
        .wr_cm_rd_ready_i   (w_cm_rdy),
        .wr_cm_rd_data_o    (w_cm_data),
        .wr_cm_rd_strb_o    (w_cm_strb),
        .wr_cm_rd_last_o    (w_cm_last),
        .rd_sch_valid_o    (w_rd_sch_v),
        .rd_sch_bank_o     (w_rd_sch_bank),
        .rd_sch_row_o      (w_rd_sch_row),
        .rd_sch_col_o      (w_rd_sch_col),
        .rd_sch_older_o    (w_rd_sch_older),
        .rd_issue_valid_i  (w_rd_issue_v),
        .rd_issue_ready_o  (w_rd_issue_rdy),
        .rd_issue_slot_i   (w_rd_issue_slot),
        .rd_dfi_ret_valid_i(w_ret_v),
        .rd_dfi_ret_ready_o(w_ret_rdy),
        .rd_dfi_ret_data_i (w_ret_data),
        .rd_dfi_ret_resp_i (w_ret_resp),
        .rd_dfi_ret_last_i (w_ret_last),
        .busy_o            ()
    );

    // ---- training-layer maintenance command channel nets ----
    logic              w_trn_cmd_req, w_trn_cmd_ack;
    dram_op_e          w_trn_cmd_op;
    logic [2:0]        w_trn_cmd_bank;
    logic [17:0]       w_trn_cmd_addr;
    logic [5:0]        w_trn_cmd_mpc;

    // ======================================================================
    // Layer 2: command scheduler
    // ======================================================================
    andesite_scheduler_layer #(
        .NUM_RANKS     (NUM_RANKS),
        .NUM_CS        (NUM_CS),
        .NUM_BANKS     (NUM_BANKS),
        .NUM_BG        (NUM_BG),
        .ROW_WIDTH     (ROW_WIDTH),
        .COL_WIDTH     (COL_WIDTH),
        .AXI_ID_WIDTH  (IW),
        .NUM_ENTRIES   (NUM_ENTRIES),
        .AGE_WIDTH     (AGE_WIDTH),
        .CMD_HISTORY_EN(CMD_HISTORY_EN),
        .HIST_T_RFC    (HIST_T_RFC_CORE),
        .HIST_T_RTW    (HIST_T_RTW_CORE),
        .HIST_T_WTR    (HIST_T_WTR_CORE),
        .CMD_DELAY     (CMD_DELAY_EFF),
        .N_LU          (N_LU)
    ) u_sched (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (page_policy_i),
        .memtype_i          (memtype_i),
        .page_mode_i        (page_mode_i),
        .page_tr_init_i     (page_tr_init_i),
        .stall_bp_o        (stall_bp_o),
        .stall_refresh_o        (stall_refresh_o),
        .stall_turnaround_o        (stall_turnaround_o),
        .stall_tccd_o        (stall_tccd_o),
        .stall_actlimit_o        (stall_actlimit_o),
        .stall_banktimer_o        (stall_banktimer_o),
        .stall_noreq_o        (stall_noreq_o),
        .stall_zq_o           (stall_zq_o),
        .stat_page_hit_o    (stat_page_hit_o),
        .stat_row_hit_o     (stat_row_hit_o),
        .stat_page_miss_o   (stat_page_miss_o),
        .stat_page_empty_o  (stat_page_empty_o),
        .stat_act_o         (stat_act_o),
        .stat_pre_o         (stat_pre_o),
        .stat_ref_o         (stat_ref_o),
        .stat_ref_busy_o    (stat_ref_busy_o),
        .t_rcd_i            (t_rcd_i),
        .t_rp_i             (t_rp_i),
        .t_ras_i            (t_ras_i),
        .t_rc_i             (t_rc_i),
        .t_wr_i             (t_wr_i),
        .t_rtp_i            (t_rtp_i),
        .t_faw_i            (t_faw_i),
        .t_rrd_i            (t_rrd_i),
        .t_wtr_i            (t_wtr_i),
        .t_rtw_i            (t_rtw_i),
        .t_ccd_i            (w_t_ccd_eff),
        .t_ccd_l_i          (t_ccd_l_i),
        .t_ccd_s_i          (t_ccd_s_i),
        .t_rrd_l_i          (t_rrd_l_i),
        .t_rrd_s_i          (t_rrd_s_i),
        .t_refi_i           (t_refi_i),
        .refi_reload_i      (refi_reload_i),
        .t_rfc_i            (t_rfc_i),
        .fgr_factor_i       (fgr_factor_i),
        .t_rfc_2x_i         (t_rfc_2x_i),
        .t_rfc_4x_i         (t_rfc_4x_i),
        .refresh_burst_i    (refresh_burst_i),
        .ref_postpone_i     (ref_postpone_i),
        .ref_pullin_i       (ref_pullin_i),
        .ref_mode_i         (ref_mode_i),
        .ref_trefi_pb_i     (ref_trefi_pb_i),
        .ref_trfc_pb_i      (ref_trfc_pb_i),
        .t_init_wait_i      (t_init_wait_i),
        .t_dll_wait_i       (t_dll_wait_i),
        .t_mrd_wait_i       (t_mrd_wait_i),
        .t_rp_wait_i        (t_rp_wait_i),
        .t_cke_wait_i       (t_cke_wait_i),
        .t_mod_wait_i       (t_mod_wait_i),
        .t_zqinit_wait_i    (t_zqinit_wait_i),
        .dram_reset_n_o     (dram_reset_n_o),
        .cke_o              (w_cke),
        .wrlvl_en_o         (w_wrlvl_en),
        .zq_enable_i        (zq_enable_i),
        .zq_interval_i      (zq_interval_i),
        .t_zqcs_i           (t_zqcs_i),
        .zq_busy_o          (zq_busy_o),
        .zq_total_o         (zq_total_o),
        .zq_interval_cnt_o  (zq_interval_cnt_o),
        .zq_overdue_o       (zq_overdue_o),
        .ref_elastic_en_i            (ref_elastic_en_i),
        .ref_pullin_idle_streak_i    (ref_pullin_idle_streak_i),
        .ref_postpone_demand_streak_i(ref_postpone_demand_streak_i),
        .ref_tcr_en_i                (ref_tcr_en_i),
        .ref_trefi_derate_i          (ref_trefi_derate_i),
        .zq_placement_i              (zq_placement_i),
        .zq_overdue_max_i            (zq_overdue_max_i),
        .t_zq_i                      (t_zq_i),
        .zq_mpc_opcode_i             (zq_mpc_opcode_i),
        .obs_ref_postpone_events_o   (obs_ref_postpone_events_o),
        .obs_ref_pullin_events_o     (obs_ref_pullin_events_o),
        .mr0_i              (mr0_i),
        .mr1_i              (mr1_i),
        .mr2_i              (mr2_i),
        .mr3_i              (mr3_i),
        .mr4_i              (mr4_i),
        .mr5_i              (mr5_i),
        .mr6_i              (mr6_i),
        .init_restart_i     (init_restart_i),
        .init_done_o        (init_done_o),
        .init_err_o         (init_err_o),
        .zq_cal_start_o     (),
        .gear_down_entry_o  (),
        .ca_train_start_o   (),
        .parity_enable_o    (w_parity_enable),
        .rtt_nom_o          (w_rtt_nom),
        .rtt_wr_o           (w_rtt_wr),
        .rtt_park_o         (w_rtt_park),
        .rd_dbi_en_o        (w_rd_dbi_en),
        .wr_dbi_en_o        (w_wr_dbi_en),
        .mpr_page_o         (),
        .fgr_factor_o       (),
        .ca_parity_lat_o    (),
        .lpddr4_odt_o       (),
        .wr_sch_valid_i     (w_wr_sch_v),
        .wr_sch_bank_i      (w_wr_sch_bank),
        .wr_sch_row_i       (w_wr_sch_row),
        .wr_sch_col_i       (w_wr_sch_col),
        .wr_sch_older_i     (w_wr_sch_older),
        .sched_order_mode_i (sched_order_mode_i),
        .sched_row_sel_i    (sched_row_sel_i),
        .sched_col_sel_i    (sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i (sched_wr_high_wm_i),
        .sched_wr_batch_max_i (sched_wr_batch_max_i),
        .sched_wr_low_wm_i  (sched_wr_low_wm_i),
        .sched_prio_sub_i   (sched_prio_sub_i),
        .sched_qos_en_i     (sched_qos_en_i),
        .rd_sch_qos_i       (w_rd_sch_qos),
        .wr_sch_qos_i       (w_wr_sch_qos),
        .wr_sch_age_exceed_i(w_wr_sch_agex),
        .wr_sch_head_rel_i  (w_wr_sch_hrel),
        .rd_sch_age_exceed_i(w_rd_sch_agex),
        .rd_sch_head_rel_i  (w_rd_sch_hrel),
        .wr_commit_ready_i  (w_wr_commit_rdy),
        .wr_commit_valid_o  (w_wr_commit_v),
        .wr_commit_slot_o   (w_wr_commit_slot),
        .rd_sch_valid_i  (w_rd_sch_v),
        .rd_sch_bank_i   (w_rd_sch_bank),
        .rd_sch_row_i    (w_rd_sch_row),
        .rd_sch_col_i    (w_rd_sch_col),
        .rd_sch_older_i  (w_rd_sch_older),
        .rd_issue_ready_i(w_rd_issue_rdy),
        .rd_issue_valid_o(w_rd_issue_v),
        .rd_issue_slot_o (w_rd_issue_slot),
        .cmd_valid_o(w_cmd_v),
        .cmd_ready_i(w_cmd_rdy),
        .cmd_op_o   (w_cmd_op),
        .cmd_rank_o (w_cmd_rank),
        .cmd_bank_o (w_cmd_bank),
        .cmd_bg_o   (w_cmd_bg),
        .cmd_row_o  (w_cmd_row),
        .cmd_col_o  (w_cmd_col),
        .cmd_ap_o   (w_cmd_ap),
        // maintenance training command channel (from training layer)
        .trn_cmd_req_i      (w_trn_cmd_req),
        .trn_cmd_ack_o      (w_trn_cmd_ack),
        .trn_cmd_op_i       (w_trn_cmd_op),
        .trn_cmd_bank_i     (w_trn_cmd_bank),
        .trn_cmd_addr_i     (w_trn_cmd_addr),
        .trn_cmd_mpc_i      (w_trn_cmd_mpc),
        .busy_o     ()
);

    // ======================================================================
    // Layer 3: training layer
    // ======================================================================
    andesite_training_layer #(
        .NUM_CS(NUM_CS)
    ) u_training (
        .mc_clk             (aclk),
        .mc_rst_n           (aresetn),
        .wrlvl_en_i         (w_wrlvl_en),
        .wrlvl_strobe_i     (wrlvl_strobe_i),
        .wrlvl_cs_sel_i     (wrlvl_cs_sel_i),
        .t_wldqsen_i        (t_wldqsen_i),
        .t_wlmrd_i          (t_wlmrd_i),
        .t_wlmrd_max_i      (t_wlmrd_max_i),
        .t_wlo_i            (t_wlo_i),
        .t_wloe_i           (t_wloe_i),
        .rdlvl_en_i         (rdlvl_en_i),
        .rdlvl_cs_sel_i     (rdlvl_cs_sel_i),
        .csr_mr3_mpr_enter_i(csr_mr3_mpr_enter_i),
        .csr_mr3_mpr_exit_i (csr_mr3_mpr_exit_i),
        .t_mpr_enter_i      (t_mpr_enter_i),
        .t_mpr_exit_i       (t_mpr_exit_i),
        .t_mpr_readout_i    (t_mpr_readout_i),
        .tmod_i             (tmod_i),
        .t_rdlvl_timeout_i  (t_rdlvl_timeout_i),
        .ca_train_en_i      (ca_train_en_i),
        .wdq_cal_en_i       (wdq_cal_en_i),
        .chan_sel_i         (chan_sel_i),
        .csr_mpc_ca_enter_i (csr_mpc_ca_enter_i),
        .csr_mpc_ca_exit_i  (csr_mpc_ca_exit_i),
        .csr_mpc_wdq_enter_i(csr_mpc_wdq_enter_i),
        .csr_mpc_wdq_exit_i (csr_mpc_wdq_exit_i),
        .t_ca_train_i       (t_ca_train_i),
        .t_wdq_cal_i        (t_wdq_cal_i),
        .t_ca_timeout_i     (t_ca_timeout_i),
        .dfi_clk            (dfi_clk),
        .dfi_rstn           (dfi_rstn),
        .dfi_phylvl_req_cs_n_o(dfi_phylvl_req_cs_n_o),
        .dfi_phylvl_ack_cs_n_i(dfi_phylvl_ack_cs_n_i),
        .dfi_phy_wrlvl_cs_n_o (dfi_phy_wrlvl_cs_n_o),
        .dfi_wrlvl_strobe_o   (dfi_wrlvl_strobe_o),
        .dfi_phylvl_ack_cs_n_o(dfi_phylvl_ack_cs_n_o),
        .dfi_phylvl_req_cs_n_i(dfi_phylvl_req_cs_n_i),
        .dfi_phy_rdlvl_cs_n_o (dfi_phy_rdlvl_cs_n_o),
        .wrlvl_prime_dq_i     (dfi_prime_dq_i),
        .mpr_pattern_i        (mpr_pattern_i),
        .ca_sample_i          (ca_sample_i),
        .wdq_sample_i         (wdq_sample_i),
        .trn_cmd_req_o        (w_trn_cmd_req),
        .trn_cmd_ack_i        (w_trn_cmd_ack),
        .trn_cmd_op_o         (w_trn_cmd_op),
        .trn_cmd_bank_o       (w_trn_cmd_bank),
        .trn_cmd_addr_o       (w_trn_cmd_addr),
        .trn_cmd_mpc_o        (w_trn_cmd_mpc),
        .wrlvl_result_valid_o (),
        .wrlvl_result_o       (),
        .wrlvl_attempts_o     (),
        .wrlvl_flips_o        (),
        .wrlvl_timeout_o      (),
        .wrlvl_ever_done_o    (),
        .wrlvl_state_o        (),
        .rdlvl_result_valid_o (),
        .rdlvl_result_o       (),
        .rdlvl_status_o       (),
        .rdlvl_attempts_o     (),
        .rdlvl_results_o      (),
        .rdlvl_timeouts_o     (),
        .rdlvl_state_o        (),
        .ca_train_result_valid_o(),
        .ca_train_result_o    (),
        .ca_train_status_o    (),
        .ca_train_attempts_o  (),
        .ca_train_results_o   (),
        .ca_train_timeouts_o  (),
        .ca_train_state_o     ()
    );

    // ---- policy outputs also exposed on core boundary ----
    assign rtt_nom_o     = w_rtt_nom;
    assign rtt_wr_o      = w_rtt_wr;
    assign rtt_park_o    = w_rtt_park;
    assign rd_dbi_en_o   = w_rd_dbi_en;
    assign wr_dbi_en_o   = w_wr_dbi_en;
    assign parity_enable_o = w_parity_enable;

    // ======================================================================
    // Layer 4: DFI layer (async CDC + datapath)
    // ======================================================================
    andesite_dfi_layer #(
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .NUM_BG          (NUM_BG),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .RD_EN_CYC       (RD_EN_CYC_CORE),
        .BL_WORDS        (RD_EN_CYC_CORE),
        .RD_MAX_OUTSTANDING(RD_RET_DEPTH),
        .RD_FIFO_DEPTH   (RD_RET_DEPTH * BURST_WORDS),
        .WD_FIFO_DEPTH   (32)
    ) u_dfi (
        .ctl_clk            (aclk),
        .ctl_rstn           (aresetn),
        .cmd_valid_i        (w_cmd_v),
        .cmd_ready_o        (w_cmd_rdy),
        .cmd_data_i         (w_cmd_data),
        .wd_valid_i         (w_cm_v),
        .wd_ready_o         (w_cm_rdy),
        .wd_data_i          (w_cm_data),
        .wd_strb_i          (w_cm_strb),
        .wd_dbi_i           ('0),
        .wd_last_i          (w_cm_last),
        .rd_valid_o         (w_ret_v),
        .rd_ready_i         (w_ret_rdy),
        .rd_data_o          (w_ret_data),
        .rd_dbi_o           (),
        .rd_resp_o          (w_ret_resp),
        .rd_last_o          (w_ret_last),
        .init_busy_i        (w_init_busy),
        .init_done_i        (init_done_o),
        .rd_dbi_en_i        (w_rd_dbi_en),
        .wr_dbi_en_i        (w_wr_dbi_en),
        .memtype_i          (memtype_i),
        .parity_en_i        (w_parity_enable),
        .gear_i             (gear_i),
        .rd_phase_i         (rd_phase_i),
        .wr_phase_i         (wr_phase_i),
        .t_phy_wrlat_i      (t_phy_wrlat_i),
        .t_rddata_en_i      (t_rddata_en_i),
        .cke_i              (w_cke),
        .dfi_clk            (dfi_clk),
        .dfi_rstn           (dfi_rstn),
        .dfi_address_o      (dfi_address_o),
        .dfi_bank_o         (dfi_bank_o),
        .dfi_bg_o           (dfi_bg_o),
        .dfi_act_n_o        (dfi_act_n_o),
        .dfi_ras_n_o        (dfi_ras_n_o),
        .dfi_cas_n_o        (dfi_cas_n_o),
        .dfi_we_n_o         (dfi_we_n_o),
        .dfi_cs_o           (dfi_cs_o),
        .dfi_cke_o          (dfi_cke_o),
        .dfi_parity_in_o    (dfi_parity_in_o),
        .dfi_wrdata_o       (dfi_wrdata_o),
        .dfi_wrdata_en_o    (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o  (dfi_wrdata_mask_o),
        .dfi_wrdata_cs_o    (dfi_wrdata_cs_o),
        .dfi_rddata_en_o    (dfi_rddata_en_o),
        .dfi_rddata_i       (dfi_rddata_i),
        .dfi_rddata_valid_i (dfi_rddata_valid_i),
        .dfi_rddata_dbi_i   (dfi_rddata_dbi_i),
        .dfi_rddata_cs_o    (dfi_rddata_cs_o),
        .dfi_init_start_o   (dfi_init_start_o),
        .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : andesite_core
