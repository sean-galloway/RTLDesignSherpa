// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_config_block
// Purpose: Project the PeakRDL-generated hwif_out struct into flat
//          mc_clk-domain config signals that mc_core (command scheduler
//          / refresh / timers / etc.) consumes; harvest obs_words from
//          the core and STATUS signals back into hwif_in. Mirrors
//          stream_config_block.sv's role.
//
//          All projection is combinational — the regblock holds its own
//          flops, so this is just bit-field unpacking and packing.

`timescale 1ns / 1ps

module ddr2_lpddr2_config_block
    import ddr2_lpddr2_csr_pkg::*;
(
    // From regblock
    input  ddr2_lpddr2_csr__out_t  hwif_out,
    output ddr2_lpddr2_csr__in_t   hwif_in,

    //=========================================================================
    // Config outputs to mc_core
    //=========================================================================
    // CTRL register
    output logic                          cfg_init_start_o,
    output logic                          cfg_init_force_restart_o,
    output logic                          cfg_pwr_req_low_power_o,
    output logic                          cfg_pwr_req_dpd_o,
    output logic                          cfg_pwr_req_active_o,
    output logic                          cfg_pwr_req_self_refresh_o,
    output logic                          cfg_soft_reset_o,

    // Packed timing parameters → individual 8/16-bit timers
    output logic [7:0]                    cfg_t_rc_o,
    output logic [7:0]                    cfg_t_rcd_o,
    output logic [7:0]                    cfg_t_rp_o,
    output logic [7:0]                    cfg_t_ras_o,
    output logic [15:0]                   cfg_t_rfc_o,
    output logic [15:0]                   cfg_t_refi_o,
    output logic [7:0]                    cfg_t_rrd_o,
    output logic [7:0]                    cfg_t_faw_o,
    output logic [7:0]                    cfg_t_wtr_o,
    output logic [7:0]                    cfg_t_ccd_o,
    output logic [7:0]                    cfg_cl_o,
    output logic [7:0]                    cfg_cwl_o,
    output logic [7:0]                    cfg_t_wr_o,
    output logic [7:0]                    cfg_t_rfcpb_o,

    // Mode registers
    output logic [15:0]                   cfg_mr0_o,
    output logic [15:0]                   cfg_mr1_o,
    output logic [15:0]                   cfg_mr2_o,
    output logic [15:0]                   cfg_mr3_o,

    // LPDDR2-specific
    output logic [7:0]                    cfg_pasr_banks_rank0_o,
    output logic [7:0]                    cfg_pasr_segs_rank0_o,

    // Scheduler / refresh / page tuning (runtime overrides)
    output logic [3:0]                    cfg_lookahead_active_o,
    output logic                          cfg_force_inorder_o,
    output logic                          cfg_happy_enable_o,
    output logic [7:0]                    cfg_age_max_runtime_o,
    output logic [7:0]                    cfg_txn_queue_high_water_o,
    output logic [1:0]                    cfg_refpb_policy_or_o,
    output logic [1:0]                    cfg_page_policy_or_o,
    output logic [3:0]                    cfg_refresh_defer_active_o,
    output logic [15:0]                   cfg_zqcs_freq_hz_o,
    output logic [1:0]                    cfg_addr_map_scheme_or_o,
    output logic [3:0]                    cfg_zq_retries_o,
    output logic [7:0]                    cfg_init_timeout_ms_o,
    output logic [15:0]                   cfg_warmup_cycles_o,
    output logic [7:0]                    cfg_hysteresis_o,

    //=========================================================================
    // Status inputs from mc_core
    //=========================================================================
    input  logic                          status_init_done_i,
    input  logic                          status_init_error_i,
    input  logic [3:0]                    status_power_state_i,
    input  logic                          status_pasr_active_i,
    input  logic [7:0]                    status_init_step_dbg_i,
    input  logic                          status_version_match_i,
    input  logic [31:0]                   status_history_i,
    input  logic [1:0]                    status_temp_class_rank0_i,

    // Build-time discovery echoes
    input  logic [3:0]                    cap_lookahead_max_i,
    input  logic [3:0]                    cap_synth_mask_i,

    //=========================================================================
    // Observation harvest: 9 obs_words from core_macro
    //=========================================================================
    input  logic [8:0][31:0]              obs_words_i,
    // Per-bank row-hit + ref-latency (NUM_BANKS=8, rank 0)
    input  logic [7:0][31:0]              obs_row_hit_i,
    input  logic [7:0][31:0]              obs_ref_latency_i,
    // System observation feed
    input  logic [31:0]                   obs_txn_queue_depth_max_i,
    input  logic [31:0]                   obs_txn_queue_depth_avg_i,
    input  logic [31:0]                   obs_refresh_pending_max_i,
    input  logic [31:0][3:0]              obs_refresh_defer_hist_i,  // 4 bins
    input  logic [31:0]                   obs_page_pred_accuracy_i,
    input  logic [31:0]                   obs_axi_r_latency_avg_i,
    input  logic [31:0]                   obs_axi_r_latency_p99_i,
    input  logic [31:0]                   obs_axi_w_latency_avg_i
);

    //=========================================================================
    // CTRL → cfg_*_o
    //=========================================================================
    assign cfg_init_start_o           = hwif_out.CTRL.init_start.value;
    assign cfg_init_force_restart_o   = hwif_out.CTRL.init_force_restart.value;
    assign cfg_pwr_req_low_power_o    = hwif_out.CTRL.pwr_req_low_power.value;
    assign cfg_pwr_req_dpd_o          = hwif_out.CTRL.pwr_req_dpd.value;
    assign cfg_pwr_req_active_o       = hwif_out.CTRL.pwr_req_active.value;
    assign cfg_pwr_req_self_refresh_o = hwif_out.CTRL.pwr_req_self_refresh.value;
    assign cfg_soft_reset_o           = hwif_out.CTRL.soft_reset.value;

    //=========================================================================
    // Packed timings → flat
    //=========================================================================
    assign cfg_t_rc_o     = hwif_out.TIMINGS_RC_RCD_RP_RAS.tRC.value;
    assign cfg_t_rcd_o    = hwif_out.TIMINGS_RC_RCD_RP_RAS.tRCD.value;
    assign cfg_t_rp_o     = hwif_out.TIMINGS_RC_RCD_RP_RAS.tRP.value;
    assign cfg_t_ras_o    = hwif_out.TIMINGS_RC_RCD_RP_RAS.tRAS.value;

    assign cfg_t_rfc_o    = hwif_out.TIMINGS_RFC_REFI.tRFC.value;
    assign cfg_t_refi_o   = hwif_out.TIMINGS_RFC_REFI.tREFI.value;

    assign cfg_t_rrd_o    = hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tRRD.value;
    assign cfg_t_faw_o    = hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tFAW.value;
    assign cfg_t_wtr_o    = hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tWTR.value;
    assign cfg_t_ccd_o    = hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tCCD.value;

    assign cfg_cl_o       = hwif_out.TIMINGS_CL_CWL_WR.CL.value;
    assign cfg_cwl_o      = hwif_out.TIMINGS_CL_CWL_WR.CWL.value;
    assign cfg_t_wr_o     = hwif_out.TIMINGS_CL_CWL_WR.tWR.value;
    assign cfg_t_rfcpb_o  = hwif_out.TIMINGS_CL_CWL_WR.tRFCpb.value;

    //=========================================================================
    // Mode registers
    //=========================================================================
    assign cfg_mr0_o = hwif_out.MR0.VAL.value;
    assign cfg_mr1_o = hwif_out.MR1.VAL.value;
    assign cfg_mr2_o = hwif_out.MR2.VAL.value;
    assign cfg_mr3_o = hwif_out.MR3.VAL.value;

    //=========================================================================
    // LPDDR2-specific
    //=========================================================================
    assign cfg_pasr_banks_rank0_o = hwif_out.PASR_BANK_MASK_RANK0.pasr_banks.value;
    assign cfg_pasr_segs_rank0_o  = hwif_out.PASR_SEG_MASK_RANK0.pasr_segs.value;

    //=========================================================================
    // Scheduler / page / refresh / addr-map / init tuning
    //=========================================================================
    assign cfg_lookahead_active_o     = hwif_out.SCHED_TUNING.lookahead_active.value;
    assign cfg_force_inorder_o        = hwif_out.SCHED_TUNING.force_inorder.value;
    assign cfg_happy_enable_o         = hwif_out.SCHED_TUNING.happy_enable.value;
    assign cfg_age_max_runtime_o      = hwif_out.SCHED_TUNING.age_max_runtime.value;
    assign cfg_txn_queue_high_water_o = hwif_out.SCHED_TUNING.txn_queue_high_water.value;
    assign cfg_warmup_cycles_o        = hwif_out.PAGE_PRED_TUNING.warmup_cycles.value;
    assign cfg_hysteresis_o           = hwif_out.PAGE_PRED_TUNING.hysteresis.value;
    assign cfg_refpb_policy_or_o      = hwif_out.REFRESH_TUNING.refpb_policy_or.value;
    assign cfg_page_policy_or_o       = hwif_out.REFRESH_TUNING.page_policy_or.value;
    assign cfg_refresh_defer_active_o = hwif_out.REFRESH_TUNING.refresh_defer_active.value;
    assign cfg_zqcs_freq_hz_o         = hwif_out.REFRESH_TUNING.zqcs_freq_hz.value;
    assign cfg_addr_map_scheme_or_o   = hwif_out.ADDR_MAP_TUNING.scheme_or.value;
    assign cfg_zq_retries_o           = hwif_out.INIT_TUNING.zq_retries.value;
    assign cfg_init_timeout_ms_o      = hwif_out.INIT_TUNING.init_timeout_ms.value;

    //=========================================================================
    // hwif_in: project status + observation back into the regblock
    //=========================================================================
    always_comb begin
        // STATUS
        hwif_in.STATUS.init_done.next     = status_init_done_i;
        hwif_in.STATUS.init_error.next    = status_init_error_i;
        hwif_in.STATUS.power_state.next   = status_power_state_i;
        hwif_in.STATUS.pasr_active.next   = status_pasr_active_i;
        hwif_in.STATUS.init_step_dbg.next = status_init_step_dbg_i;
        hwif_in.STATUS.version_match.next = status_version_match_i;

        hwif_in.STATUS_HISTORY.history.next = status_history_i;

        hwif_in.TEMP_DERATE_RANK0.temp_class.next = status_temp_class_rank0_i;

        // Build-time discovery echoes (RO observed fields)
        hwif_in.SCHED_TUNING.lookahead_max_obs.next   = cap_lookahead_max_i;
        hwif_in.ADDR_MAP_TUNING.synth_mask_obs.next   = cap_synth_mask_i;

        // Per-bank observation (rank 0, NUM_BANKS=8)
        for (int b = 0; b < 8; b++) begin
            hwif_in.OBS_ROW_HIT[b].ROW_HIT.VAL.next     = obs_row_hit_i[b];
            hwif_in.OBS_REF_LATENCY[b].REF_LAT.VAL.next = obs_ref_latency_i[b];
        end

        // System observation
        hwif_in.OBS_TXN_QUEUE_DEPTH_MAX.VAL.next  = obs_txn_queue_depth_max_i;
        hwif_in.OBS_TXN_QUEUE_DEPTH_AVG.VAL.next  = obs_txn_queue_depth_avg_i;
        hwif_in.OBS_REFRESH_PENDING_MAX.VAL.next  = obs_refresh_pending_max_i;
        hwif_in.OBS_REFRESH_DEFER_HIST_0.VAL.next = obs_refresh_defer_hist_i[0];
        hwif_in.OBS_REFRESH_DEFER_HIST_1.VAL.next = obs_refresh_defer_hist_i[1];
        hwif_in.OBS_REFRESH_DEFER_HIST_2.VAL.next = obs_refresh_defer_hist_i[2];
        hwif_in.OBS_REFRESH_DEFER_HIST_3.VAL.next = obs_refresh_defer_hist_i[3];
        hwif_in.OBS_PAGE_PRED_ACCURACY.VAL.next   = obs_page_pred_accuracy_i;
        hwif_in.OBS_AXI_R_LATENCY_AVG.VAL.next    = obs_axi_r_latency_avg_i;
        hwif_in.OBS_AXI_R_LATENCY_P99.VAL.next    = obs_axi_r_latency_p99_i;
        hwif_in.OBS_AXI_W_LATENCY_AVG.VAL.next    = obs_axi_w_latency_avg_i;

        // obs_* harvest words (from command_scheduler_macro + axi_frontend_macro)
        for (int w = 0; w < 9; w++) begin
            hwif_in.OBS_WORDS[w].WORD.VAL.next = obs_words_i[w];
        end
    end

endmodule : ddr2_lpddr2_config_block
