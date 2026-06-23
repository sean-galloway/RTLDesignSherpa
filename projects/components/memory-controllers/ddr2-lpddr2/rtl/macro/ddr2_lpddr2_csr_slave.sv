// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_csr_slave
// Purpose: APB CSR slave for the DDR2/LPDDR2 memory controller. This
//          is the complete configuration top — it contains the APB
//          protocol layer, CDC, CMD/RSP conversion, PeakRDL register
//          block, AND the config_block projection. The public ports
//          are APB + flat cfg_*_o + status feed inputs + obs_words
//          feed inputs. Nothing about the hwif struct leaks out.
//
//          A higher-level wrapper just connects this slave's cfg_*_o
//          straight into ddr2_lpddr2_core_macro and routes the core's
//          status + obs_words back into the slave's *_i ports.
//
// Internal stack:
//   1. apb_slave_cdc            — APB (pclk) → CMD/RSP (mc_clk) CDC
//   2. peakrdl_to_cmdrsp        — CMD/RSP → PeakRDL passthrough adapter
//   3. ddr2_lpddr2_csr          — PeakRDL-generated register block
//   4. ddr2_lpddr2_config_block — hwif_out → cfg_*_o + status/obs → hwif_in
//
// CSR map: docs/ddr2_lpddr2_has/ch06_integration/03_csr_map.md
// RDL src: rtl/macro/ddr2_lpddr2_csr.rdl
// obs layout: docs/csr_obs_layout.md (obs_words readback at 0x1C0+)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ddr2_lpddr2_csr_slave
    import ddr2_lpddr2_csr_pkg::*;
#(
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int APB_STRB_WIDTH = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH = 3
) (
    // mc_clk-domain reset + clock
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    // APB-domain clock + reset
    input  logic                          pclk,
    input  logic                          presetn,

    // APB slave port
    input  logic                          s_apb_PSEL,
    input  logic                          s_apb_PENABLE,
    output logic                          s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_PADDR,
    input  logic                          s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_apb_PRDATA,
    output logic                          s_apb_PSLVERR,

    //=========================================================================
    // Flat config outputs → mc_core / scheduler / refresh / timers
    //=========================================================================
    output logic                          cfg_init_start_o,
    output logic                          cfg_init_force_restart_o,
    output logic                          cfg_pwr_req_low_power_o,
    output logic                          cfg_pwr_req_dpd_o,
    output logic                          cfg_pwr_req_active_o,
    output logic                          cfg_pwr_req_self_refresh_o,
    output logic                          cfg_soft_reset_o,

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

    output logic [15:0]                   cfg_mr0_o,
    output logic [15:0]                   cfg_mr1_o,
    output logic [15:0]                   cfg_mr2_o,
    output logic [15:0]                   cfg_mr3_o,

    output logic [7:0]                    cfg_pasr_banks_rank0_o,
    output logic [7:0]                    cfg_pasr_segs_rank0_o,

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
    // Status feed inputs ← mc_core
    //=========================================================================
    input  logic                          status_init_done_i,
    input  logic                          status_init_error_i,
    input  logic [3:0]                    status_power_state_i,
    input  logic                          status_pasr_active_i,
    input  logic [7:0]                    status_init_step_dbg_i,
    input  logic                          status_version_match_i,
    input  logic [31:0]                   status_history_i,
    input  logic [1:0]                    status_temp_class_rank0_i,
    input  logic [3:0]                    cap_lookahead_max_i,
    input  logic [3:0]                    cap_synth_mask_i,

    //=========================================================================
    // obs_* feed inputs ← mc_core / axi_frontend
    //=========================================================================
    input  logic [8:0][31:0]              obs_words_i,
    input  logic [7:0][31:0]              obs_row_hit_i,
    input  logic [7:0][31:0]              obs_ref_latency_i,
    input  logic [31:0]                   obs_txn_queue_depth_max_i,
    input  logic [31:0]                   obs_txn_queue_depth_avg_i,
    input  logic [31:0]                   obs_refresh_pending_max_i,
    input  logic [3:0][31:0]              obs_refresh_defer_hist_i,
    input  logic [31:0]                   obs_page_pred_accuracy_i,
    input  logic [31:0]                   obs_axi_r_latency_avg_i,
    input  logic [31:0]                   obs_axi_r_latency_p99_i,
    input  logic [31:0]                   obs_axi_w_latency_avg_i
);

    //=========================================================================
    // 1. APB → CMD/RSP with CDC (pclk → mc_clk)
    //=========================================================================
    logic                          cmd_valid;
    logic                          cmd_ready;
    logic                          cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     cmd_pwdata;
    logic [APB_STRB_WIDTH-1:0]     cmd_pstrb;
    logic [APB_PROT_WIDTH-1:0]     cmd_pprot;

    logic                          rsp_valid;
    logic                          rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     rsp_prdata;
    logic                          rsp_pslverr;

    apb_slave_cdc #(
        .ADDR_WIDTH      (APB_ADDR_WIDTH),
        .DATA_WIDTH      (APB_DATA_WIDTH),
        .STRB_WIDTH      (APB_STRB_WIDTH),
        .PROT_WIDTH      (APB_PROT_WIDTH),
        .USE_2_PHASE_CDC (1'b1)
    ) u_apb_slave_cdc (
        .aclk             (mc_clk),
        .aresetn          (mc_rst_n),
        .pclk             (pclk),
        .presetn          (presetn),
        .s_apb_PSEL       (s_apb_PSEL),
        .s_apb_PENABLE    (s_apb_PENABLE),
        .s_apb_PREADY     (s_apb_PREADY),
        .s_apb_PADDR      (s_apb_PADDR),
        .s_apb_PWRITE     (s_apb_PWRITE),
        .s_apb_PWDATA     (s_apb_PWDATA),
        .s_apb_PSTRB      (s_apb_PSTRB),
        .s_apb_PPROT      (s_apb_PPROT),
        .s_apb_PRDATA     (s_apb_PRDATA),
        .s_apb_PSLVERR    (s_apb_PSLVERR),
        .cmd_valid        (cmd_valid),
        .cmd_ready        (cmd_ready),
        .cmd_pwrite       (cmd_pwrite),
        .cmd_paddr        (cmd_paddr),
        .cmd_pwdata       (cmd_pwdata),
        .cmd_pstrb        (cmd_pstrb),
        .cmd_pprot        (cmd_pprot),
        .rsp_valid        (rsp_valid),
        .rsp_ready        (rsp_ready),
        .rsp_prdata       (rsp_prdata),
        .rsp_pslverr      (rsp_pslverr)
    );

    //=========================================================================
    // 2. CMD/RSP → PeakRDL passthrough adapter
    //=========================================================================
    logic                          regblk_req;
    logic                          regblk_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]     regblk_addr;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_data;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_biten;
    logic                          regblk_req_stall_wr;
    logic                          regblk_req_stall_rd;
    logic                          regblk_rd_ack;
    logic                          regblk_rd_err;
    logic [APB_DATA_WIDTH-1:0]     regblk_rd_data;
    logic                          regblk_wr_ack;
    logic                          regblk_wr_err;

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_peakrdl_adapter (
        .aclk                 (mc_clk),
        .aresetn              (mc_rst_n),
        .cmd_valid            (cmd_valid),
        .cmd_ready            (cmd_ready),
        .cmd_pwrite           (cmd_pwrite),
        .cmd_paddr            (cmd_paddr),
        .cmd_pwdata           (cmd_pwdata),
        .cmd_pstrb            (cmd_pstrb),
        .rsp_valid            (rsp_valid),
        .rsp_ready            (rsp_ready),
        .rsp_prdata           (rsp_prdata),
        .rsp_pslverr          (rsp_pslverr),
        .regblk_req           (regblk_req),
        .regblk_req_is_wr     (regblk_req_is_wr),
        .regblk_addr          (regblk_addr),
        .regblk_wr_data       (regblk_wr_data),
        .regblk_wr_biten      (regblk_wr_biten),
        .regblk_req_stall_wr  (regblk_req_stall_wr),
        .regblk_req_stall_rd  (regblk_req_stall_rd),
        .regblk_rd_ack        (regblk_rd_ack),
        .regblk_rd_err        (regblk_rd_err),
        .regblk_rd_data       (regblk_rd_data),
        .regblk_wr_ack        (regblk_wr_ack),
        .regblk_wr_err        (regblk_wr_err)
    );

    //=========================================================================
    // 3. PeakRDL register block (internal hwif structs)
    //=========================================================================
    ddr2_lpddr2_csr__in_t   hwif_in;
    ddr2_lpddr2_csr__out_t  hwif_out;

    ddr2_lpddr2_csr u_regs (
        .clk                  (mc_clk),
        .rst                  (~mc_rst_n),
        .s_cpuif_req          (regblk_req),
        .s_cpuif_req_is_wr    (regblk_req_is_wr),
        .s_cpuif_addr         (regblk_addr),
        .s_cpuif_wr_data      (regblk_wr_data),
        .s_cpuif_wr_biten     (regblk_wr_biten),
        .s_cpuif_req_stall_wr (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd (regblk_req_stall_rd),
        .s_cpuif_rd_ack       (regblk_rd_ack),
        .s_cpuif_rd_err       (regblk_rd_err),
        .s_cpuif_rd_data      (regblk_rd_data),
        .s_cpuif_wr_ack       (regblk_wr_ack),
        .s_cpuif_wr_err       (regblk_wr_err),
        .hwif_in              (hwif_in),
        .hwif_out             (hwif_out)
    );

    //=========================================================================
    // 4. Config / status / observation projection (hwif ↔ flat ports)
    //=========================================================================
    ddr2_lpddr2_config_block u_config_block (
        .hwif_out                    (hwif_out),
        .hwif_in                     (hwif_in),

        .cfg_init_start_o            (cfg_init_start_o),
        .cfg_init_force_restart_o    (cfg_init_force_restart_o),
        .cfg_pwr_req_low_power_o     (cfg_pwr_req_low_power_o),
        .cfg_pwr_req_dpd_o           (cfg_pwr_req_dpd_o),
        .cfg_pwr_req_active_o        (cfg_pwr_req_active_o),
        .cfg_pwr_req_self_refresh_o  (cfg_pwr_req_self_refresh_o),
        .cfg_soft_reset_o            (cfg_soft_reset_o),

        .cfg_t_rc_o                  (cfg_t_rc_o),
        .cfg_t_rcd_o                 (cfg_t_rcd_o),
        .cfg_t_rp_o                  (cfg_t_rp_o),
        .cfg_t_ras_o                 (cfg_t_ras_o),
        .cfg_t_rfc_o                 (cfg_t_rfc_o),
        .cfg_t_refi_o                (cfg_t_refi_o),
        .cfg_t_rrd_o                 (cfg_t_rrd_o),
        .cfg_t_faw_o                 (cfg_t_faw_o),
        .cfg_t_wtr_o                 (cfg_t_wtr_o),
        .cfg_t_ccd_o                 (cfg_t_ccd_o),
        .cfg_cl_o                    (cfg_cl_o),
        .cfg_cwl_o                   (cfg_cwl_o),
        .cfg_t_wr_o                  (cfg_t_wr_o),
        .cfg_t_rfcpb_o               (cfg_t_rfcpb_o),

        .cfg_mr0_o                   (cfg_mr0_o),
        .cfg_mr1_o                   (cfg_mr1_o),
        .cfg_mr2_o                   (cfg_mr2_o),
        .cfg_mr3_o                   (cfg_mr3_o),

        .cfg_pasr_banks_rank0_o      (cfg_pasr_banks_rank0_o),
        .cfg_pasr_segs_rank0_o       (cfg_pasr_segs_rank0_o),

        .cfg_lookahead_active_o      (cfg_lookahead_active_o),
        .cfg_force_inorder_o         (cfg_force_inorder_o),
        .cfg_happy_enable_o          (cfg_happy_enable_o),
        .cfg_age_max_runtime_o       (cfg_age_max_runtime_o),
        .cfg_txn_queue_high_water_o  (cfg_txn_queue_high_water_o),
        .cfg_refpb_policy_or_o       (cfg_refpb_policy_or_o),
        .cfg_page_policy_or_o        (cfg_page_policy_or_o),
        .cfg_refresh_defer_active_o  (cfg_refresh_defer_active_o),
        .cfg_zqcs_freq_hz_o          (cfg_zqcs_freq_hz_o),
        .cfg_addr_map_scheme_or_o    (cfg_addr_map_scheme_or_o),
        .cfg_zq_retries_o            (cfg_zq_retries_o),
        .cfg_init_timeout_ms_o       (cfg_init_timeout_ms_o),
        .cfg_warmup_cycles_o         (cfg_warmup_cycles_o),
        .cfg_hysteresis_o            (cfg_hysteresis_o),

        .status_init_done_i          (status_init_done_i),
        .status_init_error_i         (status_init_error_i),
        .status_power_state_i        (status_power_state_i),
        .status_pasr_active_i        (status_pasr_active_i),
        .status_init_step_dbg_i      (status_init_step_dbg_i),
        .status_version_match_i      (status_version_match_i),
        .status_history_i            (status_history_i),
        .status_temp_class_rank0_i   (status_temp_class_rank0_i),
        .cap_lookahead_max_i         (cap_lookahead_max_i),
        .cap_synth_mask_i            (cap_synth_mask_i),

        .obs_words_i                 (obs_words_i),
        .obs_row_hit_i               (obs_row_hit_i),
        .obs_ref_latency_i           (obs_ref_latency_i),
        .obs_txn_queue_depth_max_i   (obs_txn_queue_depth_max_i),
        .obs_txn_queue_depth_avg_i   (obs_txn_queue_depth_avg_i),
        .obs_refresh_pending_max_i   (obs_refresh_pending_max_i),
        .obs_refresh_defer_hist_i    (obs_refresh_defer_hist_i),
        .obs_page_pred_accuracy_i    (obs_page_pred_accuracy_i),
        .obs_axi_r_latency_avg_i     (obs_axi_r_latency_avg_i),
        .obs_axi_r_latency_p99_i     (obs_axi_r_latency_p99_i),
        .obs_axi_w_latency_avg_i     (obs_axi_w_latency_avg_i)
    );

    // PSTRB and PPROT not consumed by the regblock — silence lint.
    wire unused_cmd = |{ cmd_pstrb, cmd_pprot };

endmodule : ddr2_lpddr2_csr_slave
