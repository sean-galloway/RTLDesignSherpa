// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: andesite_core_tb
// Purpose: cocotb-side DV wrapper around andesite_core. Two jobs, both of them
//          naming conventions rather than logic:
//
//          1. The DFI 4.0 bus is aliased onto `phy_dfi_*` nets, because that is
//             what the CocoTBFramework `DFISlavePHY` BFM binds to -- it builds
//             its bus as `f"{side}_dfi"` with side fixed to "phy", so the
//             names are not negotiable from the Python side. andesite_core's
//             own ports are `dfi_*_o` / `dfi_*_i`.
//
//          2. andesite_core's observable counters (stall_*, stat_*, zq_*,
//             init_*, policy outputs, ...) are brought out as INTERNAL nets
//             rather than left dangling.
//
//          andesite_core already takes its configuration on direct ports, so
//          the TB drives them and the CSR path is andesite_top's problem.

`timescale 1ns / 1ps

module andesite_core_tb
    import andesite_pkg::*;
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
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int BGW  = (NUM_BG > 1) ? $clog2(NUM_BG) : 1,
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int UW   = 1,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DW   = DFI_DATA_WIDTH,
    parameter int SW   = DW / 8,
    parameter int PHW  = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int DFI_STRB_WIDTH  = DW / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W  = ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = BKW * DFI_RATE,
    parameter int DFI_BG_BUS_W    = BGW * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W    = NUM_RANKS * DFI_RATE
) (
    input logic aclk,
    input logic aresetn,
    input logic dfi_clk,
    input logic dfi_rstn,
    input memtype_e memtype_i,
    input page_policy_e page_policy_i,
    input logic [2:0] page_mode_i,
    input logic [7:0] page_tr_init_i,
    input logic [1:0] sched_order_mode_i,
    input logic [1:0] sched_row_sel_i,
    input logic [1:0] sched_col_sel_i,
    input logic [1:0] sched_access_pref_i,
    input logic [7:0] sched_wr_high_wm_i,
    input logic [7:0] sched_wr_batch_max_i,
    input logic [7:0] sched_wr_low_wm_i,
    input logic [1:0] sched_prio_sub_i,
    input logic sched_qos_en_i,
    input logic [7:0] sched_age_thresh_i,
    input logic [4:0] bank_lsb_i,
    input logic hash_en_i,
    input logic [7:0] hash_seed_i,
    input logic [7:0] t_rcd_i,
    input logic [7:0] t_rp_i,
    input logic [7:0] t_ras_i,
    input logic [7:0] t_rc_i,
    input logic [7:0] t_wr_i,
    input logic [7:0] t_rtp_i,
    input logic [7:0] t_faw_i,
    input logic [7:0] t_rrd_i,
    input logic [7:0] t_wtr_i,
    input logic [7:0] t_rtw_i,
    input logic [7:0] t_ccd_i,
    input logic [7:0] t_ccd_l_i,
    input logic [7:0] t_ccd_s_i,
    input logic [7:0] t_rrd_l_i,
    input logic [7:0] t_rrd_s_i,
    input logic [15:0] t_refi_i,
    input logic refi_reload_i,
    input logic [15:0] t_rfc_i,
    input logic [1:0] fgr_factor_i,
    input logic [15:0] t_rfc_2x_i,
    input logic [15:0] t_rfc_4x_i,
    input logic [3:0] refresh_burst_i,
    input logic [3:0] ref_postpone_i,
    input logic [3:0] ref_pullin_i,
    input logic [1:0] ref_mode_i,
    input logic [15:0] ref_trefi_pb_i,
    input logic [7:0] ref_trfc_pb_i,
    input logic [15:0] t_init_wait_i,
    input logic [15:0] t_dll_wait_i,
    input logic [7:0] t_mrd_wait_i,
    input logic [7:0] t_rp_wait_i,
    input logic [15:0] t_cke_wait_i,
    input logic [15:0] t_mod_wait_i,
    input logic [15:0] t_zqinit_wait_i,
    input logic zq_enable_i,
    input logic [31:0] zq_interval_i,
    input logic [15:0] t_zqcs_i,
    input logic [15:0] t_zq_i,
    input logic [5:0] zq_mpc_opcode_i,
    input logic ref_elastic_en_i,
    input logic [7:0] ref_pullin_idle_streak_i,
    input logic [6:0] ref_postpone_demand_streak_i,
    input logic ref_tcr_en_i,
    input logic [1:0] ref_trefi_derate_i,
    input logic [1:0] zq_placement_i,
    input logic [12:0] zq_overdue_max_i,
    input logic wrlvl_strobe_i,
    input logic [3:0] wrlvl_cs_sel_i,
    input logic [15:0] t_wldqsen_i,
    input logic [15:0] t_wlmrd_i,
    input logic [15:0] t_wlmrd_max_i,
    input logic [15:0] t_wlo_i,
    input logic [15:0] t_wloe_i,
    input logic dfi_prime_dq_i,
    input logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_i,
    input logic rdlvl_en_i,
    input logic [3:0] rdlvl_cs_sel_i,
    input logic [15:0] csr_mr3_mpr_enter_i,
    input logic [15:0] csr_mr3_mpr_exit_i,
    input logic [15:0] t_mpr_enter_i,
    input logic [15:0] t_mpr_exit_i,
    input logic [15:0] t_mpr_readout_i,
    input logic [15:0] tmod_i,
    input logic [15:0] t_rdlvl_timeout_i,
    input logic mpr_pattern_i,
    input logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_i,
    input logic ca_train_en_i,
    input logic wdq_cal_en_i,
    input logic chan_sel_i,
    input logic [15:0] csr_mpc_ca_enter_i,
    input logic [15:0] csr_mpc_ca_exit_i,
    input logic [15:0] csr_mpc_wdq_enter_i,
    input logic [15:0] csr_mpc_wdq_exit_i,
    input logic [15:0] t_ca_train_i,
    input logic [15:0] t_wdq_cal_i,
    input logic [15:0] t_ca_timeout_i,
    input logic ca_sample_i,
    input logic wdq_sample_i,
    input logic [15:0] mr0_i,
    input logic [15:0] mr1_i,
    input logic [15:0] mr2_i,
    input logic [15:0] mr3_i,
    input logic [15:0] mr4_i,
    input logic [15:0] mr5_i,
    input logic [15:0] mr6_i,
    input logic init_restart_i,
    input logic [PHW-1:0] rd_phase_i,
    input logic [PHW-1:0] wr_phase_i,
    input logic [7:0] t_phy_wrlat_i,
    input logic [7:0] t_rddata_en_i,
    input logic [1:0] gear_i,
    input logic [3:0] bl_i,
    input logic [IW-1:0] s_axi_awid,
    input logic [AW-1:0] s_axi_awaddr,
    input logic [7:0] s_axi_awlen,
    input logic [2:0] s_axi_awsize,
    input logic [1:0] s_axi_awburst,
    input logic s_axi_awlock,
    input logic [3:0] s_axi_awcache,
    input logic [2:0] s_axi_awprot,
    input logic [3:0] s_axi_awqos,
    input logic [3:0] s_axi_awregion,
    input logic [UW-1:0] s_axi_awuser,
    input logic s_axi_awvalid,
    output logic s_axi_awready,
    input logic [DW-1:0] s_axi_wdata,
    input logic [SW-1:0] s_axi_wstrb,
    input logic s_axi_wlast,
    input logic [UW-1:0] s_axi_wuser,
    input logic s_axi_wvalid,
    output logic s_axi_wready,
    output logic [IW-1:0] s_axi_bid,
    output logic [1:0] s_axi_bresp,
    output logic [UW-1:0] s_axi_buser,
    output logic s_axi_bvalid,
    input logic s_axi_bready,
    input logic [IW-1:0] s_axi_arid,
    input logic [AW-1:0] s_axi_araddr,
    input logic [7:0] s_axi_arlen,
    input logic [2:0] s_axi_arsize,
    input logic [1:0] s_axi_arburst,
    input logic s_axi_arlock,
    input logic [3:0] s_axi_arcache,
    input logic [2:0] s_axi_arprot,
    input logic [3:0] s_axi_arqos,
    input logic [3:0] s_axi_arregion,
    input logic [UW-1:0] s_axi_aruser,
    input logic s_axi_arvalid,
    output logic s_axi_arready,
    output logic [IW-1:0] s_axi_rid,
    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0] s_axi_rresp,
    output logic s_axi_rlast,
    output logic [UW-1:0] s_axi_ruser,
    output logic s_axi_rvalid,
    input logic s_axi_rready
);

    // ---- observable counters: brought out, never dangled ------------------
    logic [31:0] stall_bp_o;
    logic [31:0] stall_refresh_o;
    logic [31:0] stall_turnaround_o;
    logic [31:0] stall_tccd_o;
    logic [31:0] stall_actlimit_o;
    logic [31:0] stall_banktimer_o;
    logic [31:0] stall_noreq_o;
    logic [31:0] stall_zq_o;
    logic [31:0] stat_page_hit_o;
    logic [31:0] stat_row_hit_o [NUM_BANKS];
    logic [31:0] stat_page_miss_o;
    logic [31:0] stat_page_empty_o;
    logic [31:0] stat_act_o;
    logic [31:0] stat_pre_o;
    logic [31:0] stat_ref_o;
    logic [31:0] stat_ref_busy_o;
    logic zq_busy_o;
    logic [15:0] zq_total_o;
    logic [31:0] zq_interval_cnt_o;
    logic zq_overdue_o;
    logic [15:0] obs_ref_postpone_events_o;
    logic [15:0] obs_ref_pullin_events_o;
    logic init_done_o;
    logic init_err_o;
    logic [2:0] rtt_nom_o;
    logic [2:0] rtt_wr_o;
    logic [2:0] rtt_park_o;
    logic rd_dbi_en_o;
    logic wr_dbi_en_o;
    logic parity_enable_o;
    logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_o;
    logic [NUM_CS-1:0] dfi_phy_wrlvl_cs_n_o;
    logic dfi_wrlvl_strobe_o;
    logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_o;
    logic [NUM_CS-1:0] dfi_phy_rdlvl_cs_n_o;

    // ---- the DFI 4.0 bus under the names DFISlavePHY binds -----------------
    // Widened to DFI_RATE * per-phase width so the BFM's phase-aware decode
    // sees the controller's phase-0 command in the low slice and NOPs in the
    // upper slices (scoria_core_tb precedent).
    logic [DFI_ADDR_BUS_W-1:0] phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0] phy_dfi_bank;
    logic [DFI_BG_BUS_W-1:0]   phy_dfi_bg;
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_act_n;
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]   phy_dfi_cs_n;
    logic                      phy_dfi_cke;
    logic                  phy_dfi_parity_in;

    // Core outputs are single-phase (DFI 4.0 per-clock command bus); expand
    // them to the multi-phase bus width the BFM expects.
    logic [ADDR_WIDTH-1:0] core_dfi_address;
    logic [BKW-1:0]        core_dfi_bank;
    logic [BGW-1:0]        core_dfi_bg;
    logic                  core_dfi_act_n;
    logic                  core_dfi_ras_n;
    logic                  core_dfi_cas_n;
    logic                  core_dfi_we_n;
    logic [NUM_RANKS-1:0]  core_dfi_cs_n;

    generate
        if (DFI_RATE > 1) begin : g_widen_cmd
            assign phy_dfi_address = { {(DFI_RATE-1){ADDR_WIDTH'(1'b0)}}, core_dfi_address };
            assign phy_dfi_bank    = { {(DFI_RATE-1){BKW'(1'b0)}},        core_dfi_bank    };
            assign phy_dfi_bg      = { {(DFI_RATE-1){BGW'(1'b0)}},        core_dfi_bg      };
            assign phy_dfi_act_n   = { {(DFI_RATE-1){1'b1}},              core_dfi_act_n   };
            assign phy_dfi_ras_n   = { {(DFI_RATE-1){1'b1}},              core_dfi_ras_n   };
            assign phy_dfi_cas_n   = { {(DFI_RATE-1){1'b1}},              core_dfi_cas_n   };
            assign phy_dfi_we_n    = { {(DFI_RATE-1){1'b1}},              core_dfi_we_n    };
            assign phy_dfi_cs_n    = { {(DFI_RATE-1){1'b1}},              core_dfi_cs_n    };
        end else begin : g_pass_cmd
            assign phy_dfi_address = core_dfi_address;
            assign phy_dfi_bank    = core_dfi_bank;
            assign phy_dfi_bg      = core_dfi_bg;
            assign phy_dfi_act_n   = core_dfi_act_n;
            assign phy_dfi_ras_n   = core_dfi_ras_n;
            assign phy_dfi_cas_n   = core_dfi_cas_n;
            assign phy_dfi_we_n    = core_dfi_we_n;
            assign phy_dfi_cs_n    = core_dfi_cs_n;
        end
    endgenerate

    logic [DFI_DATA_WIDTH-1:0] phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]   phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0] phy_dfi_wrdata_mask;
    logic [NUM_RANKS-1:0]      phy_dfi_wrdata_cs;
    logic [DFI_EN_WIDTH-1:0]   phy_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0] phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0] phy_dfi_rddata_valid;
    logic [DFI_STRB_WIDTH-1:0] phy_dfi_rddata_dbi;
    logic [NUM_RANKS-1:0]      phy_dfi_rddata_cs;
    logic                      phy_dfi_init_start;
    logic                      phy_dfi_init_complete;

    // DFI signals andesite_core does not drive. The BFM expects the full v4.0
    // signal set, so they are declared and tied off here rather than omitted.
    logic                  phy_dfi_reset_n;
    logic [NUM_RANKS-1:0]  phy_dfi_odt;
    logic                  phy_dfi_error, phy_dfi_error_info;
    logic                  phy_dfi_crc_alert;
    logic                  phy_dfi_ctrlupd_req, phy_dfi_ctrlupd_ack;
    logic                  phy_dfi_phyupd_req, phy_dfi_phyupd_ack;
    logic [1:0]            phy_dfi_phyupd_type;
    logic                  phy_dfi_disconnect_req;
    logic                  phy_dfi_freq_change_req, phy_dfi_freq_change_ack;
    logic                  phy_dfi_parity_check, phy_dfi_phymstr_req;
    logic                  phy_dfi_training_active, phy_dfi_training_phase;
    logic [DFI_CS_BUS_W-1:0] phy_dfi_dram_clk_disable;

    assign phy_dfi_odt              = '0;
    assign phy_dfi_error            = 1'b0;
    assign phy_dfi_error_info       = 1'b0;
    assign phy_dfi_crc_alert        = 1'b0;
    assign phy_dfi_ctrlupd_req      = 1'b0;
    assign phy_dfi_ctrlupd_ack      = 1'b0;
    assign phy_dfi_phyupd_req       = 1'b0;
    assign phy_dfi_phyupd_ack       = 1'b0;
    assign phy_dfi_phyupd_type      = 2'b0;
    assign phy_dfi_disconnect_req   = 1'b0;
    assign phy_dfi_freq_change_req  = 1'b0;
    assign phy_dfi_freq_change_ack  = 1'b0;
    assign phy_dfi_parity_check     = 1'b0;
    assign phy_dfi_phymstr_req      = 1'b0;
    assign phy_dfi_training_active  = 1'b0;
    assign phy_dfi_training_phase   = 1'b0;
    assign phy_dfi_dram_clk_disable = '0;

    // ---- the DUT -----------------------------------------------------------
    andesite_core #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .NUM_BG(NUM_BG),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .ADDR_WIDTH(ADDR_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH(DRAM_DEVICE_WIDTH), .DRAM_BL(DRAM_BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS),
        .RD_RET_DEPTH(RD_RET_DEPTH), .CMD_DELAY(CMD_DELAY),
        .AGE_WIDTH(AGE_WIDTH), .CMD_HISTORY_EN(CMD_HISTORY_EN),
        .HIST_T_RFC_CORE(HIST_T_RFC_CORE),
        .HIST_T_RTW_CORE(HIST_T_RTW_CORE),
        .HIST_T_WTR_CORE(HIST_T_WTR_CORE)
    ) u_core (
        .*,
        .dfi_address_o       (core_dfi_address),
        .dfi_bank_o          (core_dfi_bank),
        .dfi_bg_o            (core_dfi_bg),
        .dfi_act_n_o         (core_dfi_act_n),
        .dfi_ras_n_o         (core_dfi_ras_n),
        .dfi_cas_n_o         (core_dfi_cas_n),
        .dfi_we_n_o          (core_dfi_we_n),
        .dfi_cs_o            (core_dfi_cs_n),
        .dfi_cke_o           (phy_dfi_cke),
        .dfi_parity_in_o     (phy_dfi_parity_in),
        .dfi_reset_n_o       (phy_dfi_reset_n),
        .dfi_wrdata_o        (phy_dfi_wrdata),
        .dfi_wrdata_en_o     (phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o   (phy_dfi_wrdata_mask),
        .dfi_wrdata_cs_o     (phy_dfi_wrdata_cs),
        .dfi_rddata_en_o     (phy_dfi_rddata_en),
        .dfi_rddata_i        (phy_dfi_rddata),
        .dfi_rddata_valid_i  (phy_dfi_rddata_valid),
        .dfi_rddata_dbi_i    (phy_dfi_rddata_dbi),
        .dfi_rddata_cs_o     (phy_dfi_rddata_cs),
        .dfi_init_start_o    (phy_dfi_init_start),
        .dfi_init_complete_i (phy_dfi_init_complete)
    );

endmodule : andesite_core_tb
