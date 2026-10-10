// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_training_layer
// Purpose: Macro-tier training orchestration: owns the three training FUBs,
//          the DFI training pins, the one-active mux, and the maintenance-class
//          command channel into the scheduler.
//
// Documentation:
//   projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Author: sean galloway
// Created: 2026-10-05 (andesite, NEW)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_training_layer
    import andesite_pkg::*;
#(
    parameter int NUM_CS = 1,
    parameter int CSW    = (NUM_CS > 1) ? $clog2(NUM_CS) : 1
)(
    input  logic             mc_clk,
    input  logic             mc_rst_n,

    // ----- write-leveling policy and CSR controls ---------------------------
    input  logic             wrlvl_en_i,       // MR1[7] mode (from mode_register)
    input  logic             wrlvl_strobe_i,
    input  logic [3:0]       wrlvl_cs_sel_i,
    input  logic [15:0]      t_wldqsen_i,
    input  logic [15:0]      t_wlmrd_i,
    input  logic [15:0]      t_wlmrd_max_i,
    input  logic [15:0]      t_wlo_i,
    input  logic [15:0]      t_wloe_i,

    // ----- read-leveling CSR controls ---------------------------------------
    input  logic             rdlvl_en_i,
    input  logic [3:0]       rdlvl_cs_sel_i,
    input  logic [15:0]      csr_mr3_mpr_enter_i,
    input  logic [15:0]      csr_mr3_mpr_exit_i,
    input  logic [15:0]      t_mpr_enter_i,
    input  logic [15:0]      t_mpr_exit_i,
    input  logic [15:0]      t_mpr_readout_i,
    input  logic [15:0]      tmod_i,
    input  logic [15:0]      t_rdlvl_timeout_i,

    // ----- CA/WDQ training CSR controls -------------------------------------
    input  logic             ca_train_en_i,
    input  logic             wdq_cal_en_i,
    input  logic             chan_sel_i,
    input  logic [15:0]      csr_mpc_ca_enter_i,
    input  logic [15:0]      csr_mpc_ca_exit_i,
    input  logic [15:0]      csr_mpc_wdq_enter_i,
    input  logic [15:0]      csr_mpc_wdq_exit_i,
    input  logic [15:0]      t_ca_train_i,
    input  logic [15:0]      t_wdq_cal_i,
    input  logic [15:0]      t_ca_timeout_i,

    // ----- PHY-side DFI training pins ---------------------------------------
    input  logic             dfi_clk,
    input  logic             dfi_rstn,
    output logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_o,  // wrlvl request to PHY
    input  logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_i,  // wrlvl ack from PHY
    output logic [NUM_CS-1:0] dfi_phy_wrlvl_cs_n_o,   // wrlvl mode select
    output logic              dfi_wrlvl_strobe_o,     // wrlvl DQS strobe
    output logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_o,  // rdlvl ack to PHY
    input  logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_i,  // rdlvl request from PHY
    output logic [NUM_CS-1:0] dfi_phy_rdlvl_cs_n_o,   // rdlvl mode select
    input  logic              wrlvl_prime_dq_i,
    input  logic              mpr_pattern_i,
    input  logic              ca_sample_i,
    input  logic              wdq_sample_i,

    // ----- maintenance-class command channel to the scheduler ---------------
    output logic              trn_cmd_req_o,
    input  logic              trn_cmd_ack_i,
    output dram_op_e          trn_cmd_op_o,
    output logic [2:0]        trn_cmd_bank_o,
    output logic [17:0]       trn_cmd_addr_o,
    output logic [5:0]        trn_cmd_mpc_o,

    // ----- write-leveling telemetry -----------------------------------------
    output logic              wrlvl_result_valid_o,
    output logic              wrlvl_result_o,
    output logic [15:0]       wrlvl_attempts_o,
    output logic [15:0]       wrlvl_flips_o,
    output logic              wrlvl_timeout_o,
    output logic              wrlvl_ever_done_o,
    output logic [2:0]        wrlvl_state_o,

    // ----- read-leveling telemetry ------------------------------------------
    output logic              rdlvl_result_valid_o,
    output logic [NUM_CS-1:0] rdlvl_result_o,
    output logic [1:0]        rdlvl_status_o,
    output logic [15:0]       rdlvl_attempts_o,
    output logic [15:0]       rdlvl_results_o,
    output logic [15:0]       rdlvl_timeouts_o,
    output logic [2:0]        rdlvl_state_o,

    // ----- CA/WDQ training telemetry ----------------------------------------
    output logic              ca_train_result_valid_o,
    output logic [1:0]        ca_train_result_o,
    output logic [1:0]        ca_train_status_o,
    output logic [15:0]       ca_train_attempts_o,
    output logic [15:0]       ca_train_results_o,
    output logic [15:0]       ca_train_timeouts_o,
    output logic [2:0]        ca_train_state_o
);

    //=========================================================================
    // One-active arbitration. Priority: wrlvl (mode) > rdlvl > ca_train.
    // One-shot requests (rdlvl, ca/wdq) are captured in pending registers so
    // firmware is not required to wait for the current mode to finish before
    // asserting the next enable. Only one flow is active at a time; the active
    // flow owns the DFI training pins and the command channel.
    //=========================================================================
    typedef enum logic [1:0] {
        ST_IDLE  = 2'd0,
        ST_WRLVL = 2'd1,
        ST_RDLVL = 2'd2,
        ST_CA    = 2'd3
    } layer_state_e;

    layer_state_e r_state, w_next_state;
    logic         r_rdlvl_pending, r_ca_pending, r_wdq_pending;
    logic         w_rdlvl_start, w_ca_start;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state         <= ST_IDLE;
            r_rdlvl_pending <= 1'b0;
            r_ca_pending    <= 1'b0;
            r_wdq_pending   <= 1'b0;
        end else begin
            r_state <= w_next_state;
            // Capture one-shot enables whenever they pulse.
            if (rdlvl_en_i)     r_rdlvl_pending <= 1'b1;
            if (ca_train_en_i)  r_ca_pending    <= 1'b1;
            if (wdq_cal_en_i)   r_wdq_pending   <= 1'b1;
            // Clear the pending flag when its flow actually starts.
            if (w_rdlvl_start)  r_rdlvl_pending <= 1'b0;
            if (w_ca_start) begin
                r_ca_pending  <= 1'b0;
                r_wdq_pending <= 1'b0;
            end
        end
    end)

    always_comb begin
        w_next_state  = r_state;
        w_rdlvl_start = 1'b0;
        w_ca_start    = 1'b0;
        unique case (r_state)
            ST_IDLE: begin
                // wrlvl is a mode: it wins whenever it is asserted and no
                // one-shot flow is currently active.
                if (wrlvl_en_i) begin
                    w_next_state = ST_WRLVL;
                end else if (r_rdlvl_pending) begin
                    w_next_state  = ST_RDLVL;
                    w_rdlvl_start = 1'b1;
                end else if (r_ca_pending || r_wdq_pending) begin
                    w_next_state = ST_CA;
                    w_ca_start   = 1'b1;
                end
            end
            ST_WRLVL: if (!wrlvl_en_i) w_next_state = ST_IDLE;
            ST_RDLVL: if (rdlvl_result_valid_o) w_next_state = ST_IDLE;
            ST_CA:    if (ca_train_result_valid_o) w_next_state = ST_IDLE;
            default:  w_next_state = ST_IDLE;
        endcase
    end

    //=========================================================================
    // Synchronized DFI -> controller signals, declared early because the wrlvl
    // FUB instantiation consumes the synchronized prime-DQ and ack inputs.
    //=========================================================================
    logic [NUM_CS-1:0] w_wrlvl_ack_n;
    logic [NUM_CS-1:0] w_rdlvl_req_n;
    logic              w_wrlvl_dq_sync;

    //=========================================================================
    // FUB instances (existing files, not modified here).
    //=========================================================================
    logic [NUM_CS-1:0] w_wrlvl_req_n, w_wrlvl_mode_n;
    logic              w_wrlvl_strobe;
    logic [NUM_CS-1:0] w_rdlvl_ack_n, w_rdlvl_cs_n;
    logic [2:0]        w_rdlvl_bank;
    logic [15:0]       w_rdlvl_addr;
    logic              w_rdlvl_cmd_req;
    dram_op_e          w_rdlvl_op;
    logic [5:0]        w_ca_mpc_op;
    logic              w_ca_cmd_req;

    andesite_wrlvl_ifc #(
        .NUM_CS(NUM_CS),
        .CSW   (CSW)
    ) u_wrlvl (
        .mc_clk                (mc_clk),
        .mc_rst_n              (mc_rst_n),
        .wrlvl_en_i            (wrlvl_en_i),
        .strobe_i              (wrlvl_strobe_i),
        .cs_sel_i              (CSW'(wrlvl_cs_sel_i)),
        .t_wldqsen_i           (t_wldqsen_i),
        .t_wlmrd_i             (t_wlmrd_i),
        .t_wlmrd_max_i         (t_wlmrd_max_i),
        .t_wlo_i               (t_wlo_i),
        .t_wloe_i              (t_wloe_i),
        .dfi_phylvl_req_cs_n_o (w_wrlvl_req_n),
        .dfi_phylvl_ack_cs_n_i (w_wrlvl_ack_n),
        .dfi_phy_wrlvl_cs_n_o  (w_wrlvl_mode_n),
        .dfi_wrlvl_strobe_o    (w_wrlvl_strobe),
        .prime_dq_i            (w_wrlvl_dq_sync),
        .result_valid_o        (wrlvl_result_valid_o),
        .result_o              (wrlvl_result_o),
        .obs_attempts_o        (wrlvl_attempts_o),
        .obs_flips_o           (wrlvl_flips_o),
        .obs_timeout_o         (wrlvl_timeout_o),
        .obs_ever_done_o       (wrlvl_ever_done_o),
        .obs_state_o           (wrlvl_state_o)
    );

    andesite_rdlvl_ifc #(
        .NUM_CS(NUM_CS),
        .CSW   (CSW)
    ) u_rdlvl (
        .mc_clk                (mc_clk),
        .mc_rst_n              (mc_rst_n),
        .rdlvl_en_i            (w_rdlvl_start),
        .cs_sel_i              (CSW'(rdlvl_cs_sel_i)),
        .csr_mr3_mpr_enter_i   (csr_mr3_mpr_enter_i),
        .csr_mr3_mpr_exit_i    (csr_mr3_mpr_exit_i),
        .t_mpr_enter_i         (t_mpr_enter_i),
        .t_mpr_exit_i          (t_mpr_exit_i),
        .t_mpr_readout_i       (t_mpr_readout_i),
        .tmod_i                (tmod_i),
        .t_rdlvl_timeout_i     (t_rdlvl_timeout_i),
        .mpr_pattern_i         (mpr_pattern_i),
        .cmd_req_o             (w_rdlvl_cmd_req),
        .cmd_ack_i             (trn_cmd_ack_i),
        .cmd_op_o              (w_rdlvl_op),
        .cmd_bank_o            (w_rdlvl_bank),
        .cmd_addr_o            (w_rdlvl_addr),
        .dfi_phylvl_req_cs_n_i (w_rdlvl_req_n),
        .dfi_phylvl_ack_cs_n_o (w_rdlvl_ack_n),
        .dfi_phy_rdlvl_cs_n_o  (w_rdlvl_cs_n),
        .result_valid_o        (rdlvl_result_valid_o),
        .result_o              (rdlvl_result_o),
        .status_o              (rdlvl_status_o),
        .obs_attempts_o        (rdlvl_attempts_o),
        .obs_results_o         (rdlvl_results_o),
        .obs_timeouts_o        (rdlvl_timeouts_o),
        .obs_state_o           (rdlvl_state_o)
    );

    andesite_ca_train_ifc u_ca_train (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .ca_train_en_i      (w_ca_start && r_ca_pending),
        .wdq_cal_en_i       (w_ca_start && !r_ca_pending && r_wdq_pending),
        .chan_sel_i         (chan_sel_i),
        .csr_mpc_ca_enter_i (csr_mpc_ca_enter_i[5:0]),
        .csr_mpc_ca_exit_i  (csr_mpc_ca_exit_i[5:0]),
        .csr_mpc_wdq_enter_i(csr_mpc_wdq_enter_i[5:0]),
        .csr_mpc_wdq_exit_i (csr_mpc_wdq_exit_i[5:0]),
        .t_ca_train_i       (t_ca_train_i),
        .t_wdq_cal_i        (t_wdq_cal_i),
        .t_ca_timeout_i     (t_ca_timeout_i),
        .ca_sample_i        (ca_sample_i),
        .wdq_sample_i       (wdq_sample_i),
        .cmd_req_o          (w_ca_cmd_req),
        .cmd_ack_i          (trn_cmd_ack_i),
        .cmd_op_o           (),                 // always OP_MPC, unused here
        .mpc_op_o           (w_ca_mpc_op),
        .result_valid_o     (ca_train_result_valid_o),
        .result_o           (ca_train_result_o),
        .status_o           (ca_train_status_o),
        .obs_attempts_o     (ca_train_attempts_o),
        .obs_results_o      (ca_train_results_o),
        .obs_timeouts_o     (ca_train_timeouts_o),
        .obs_state_o        (ca_train_state_o)
    );

    // Command channel mux: only the active one-shot flow drives it.
    assign trn_cmd_req_o = (r_state == ST_RDLVL) ? w_rdlvl_cmd_req
                         : (r_state == ST_CA)    ? w_ca_cmd_req
                         : 1'b0;
    assign trn_cmd_op_o  = (r_state == ST_RDLVL) ? w_rdlvl_op
                         : (r_state == ST_CA)    ? OP_MPC
                         : OP_NOP;
    assign trn_cmd_bank_o = (r_state == ST_RDLVL) ? w_rdlvl_bank : 3'b0;
    assign trn_cmd_addr_o = (r_state == ST_RDLVL) ? {2'b0, w_rdlvl_addr}
                          : (r_state == ST_CA)    ? {12'b0, w_ca_mpc_op}
                          : 18'b0;
    assign trn_cmd_mpc_o  = (r_state == ST_CA) ? w_ca_mpc_op : 6'b0;

    //=========================================================================
    // DFI training pin mux (controller domain).
    //=========================================================================
    logic [NUM_CS-1:0] w_dfi_req_n, w_dfi_wrlvl_cs_n;
    logic              w_dfi_strobe;
    logic [NUM_CS-1:0] w_dfi_ack_n, w_dfi_rdlvl_cs_n;

    always_comb begin
        w_dfi_req_n      = '1;
        w_dfi_wrlvl_cs_n = '1;
        w_dfi_strobe     = 1'b0;
        w_dfi_ack_n      = '1;
        w_dfi_rdlvl_cs_n = '1;
        unique case (r_state)
            ST_WRLVL: begin
                w_dfi_req_n      = w_wrlvl_req_n;
                w_dfi_wrlvl_cs_n = w_wrlvl_mode_n;
                w_dfi_strobe     = w_wrlvl_strobe;
            end
            ST_RDLVL: begin
                w_dfi_ack_n      = w_rdlvl_ack_n;
                w_dfi_rdlvl_cs_n = w_rdlvl_cs_n;
            end
            default: ;
        endcase
    end

    //=========================================================================
    // Clock-domain crossing: controller -> DFI.
    // Active-low signals are inverted to active-high internally because the
    // synchronizers settle to zero out of reset; a _n feed would read asserted
    // for the first destination cycles.
    //=========================================================================
    logic [NUM_CS-1:0] w_wl_req_h,  w_wl_req_h_sync;
    logic [NUM_CS-1:0] w_wl_mode_h, w_wl_mode_h_sync;
    logic [NUM_CS-1:0] w_rl_ack_h,  w_rl_ack_h_sync;
    logic [NUM_CS-1:0] w_rl_cs_h,   w_rl_cs_h_sync;

    assign w_wl_req_h  = ~w_dfi_req_n;
    assign w_wl_mode_h = ~w_dfi_wrlvl_cs_n;
    assign w_rl_ack_h  = ~w_dfi_ack_n;
    assign w_rl_cs_h   = ~w_dfi_rdlvl_cs_n;

    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_wl_req_sync (
        .clk      (dfi_clk),
        .rst_n    (dfi_rstn),
        .async_in (w_wl_req_h),
        .sync_out (w_wl_req_h_sync)
    );
    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_wl_mode_sync (
        .clk      (dfi_clk),
        .rst_n    (dfi_rstn),
        .async_in (w_wl_mode_h),
        .sync_out (w_wl_mode_h_sync)
    );
    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_rl_ack_sync (
        .clk      (dfi_clk),
        .rst_n    (dfi_rstn),
        .async_in (w_rl_ack_h),
        .sync_out (w_rl_ack_h_sync)
    );
    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_rl_cs_sync (
        .clk      (dfi_clk),
        .rst_n    (dfi_rstn),
        .async_in (w_rl_cs_h),
        .sync_out (w_rl_cs_h_sync)
    );

    assign dfi_phylvl_req_cs_n_o = ~w_wl_req_h_sync;
    assign dfi_phy_wrlvl_cs_n_o  = ~w_wl_mode_h_sync;
    assign dfi_phylvl_ack_cs_n_o = ~w_rl_ack_h_sync;
    assign dfi_phy_rdlvl_cs_n_o  = ~w_rl_cs_h_sync;

    sync_pulse #(.SYNC_STAGES(3)) u_wl_strobe_sync (
        .i_src_clk   (mc_clk),
        .i_src_rst_n (mc_rst_n),
        .i_pulse     (w_dfi_strobe),
        .i_dst_clk   (dfi_clk),
        .i_dst_rst_n (dfi_rstn),
        .o_pulse     (dfi_wrlvl_strobe_o)
    );

    //=========================================================================
    // Clock-domain crossing: DFI -> controller.
    //=========================================================================
    logic [NUM_CS-1:0] w_wl_ack_h, w_wl_ack_h_sync;
    logic [NUM_CS-1:0] w_rl_req_h, w_rl_req_h_sync;
    logic              w_wl_dq_sync;

    assign w_wl_ack_h = ~dfi_phylvl_ack_cs_n_i;
    assign w_rl_req_h = ~dfi_phylvl_req_cs_n_i;

    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_wl_ack_sync (
        .clk      (mc_clk),
        .rst_n    (mc_rst_n),
        .async_in (w_wl_ack_h),
        .sync_out (w_wl_ack_h_sync)
    );
    cdc_synchronizer #(.WIDTH(NUM_CS), .FLOP_COUNT(3)) u_rl_req_sync (
        .clk      (mc_clk),
        .rst_n    (mc_rst_n),
        .async_in (w_rl_req_h),
        .sync_out (w_rl_req_h_sync)
    );
    cdc_synchronizer #(.WIDTH(1), .FLOP_COUNT(3)) u_wl_dq_sync (
        .clk      (mc_clk),
        .rst_n    (mc_rst_n),
        .async_in (wrlvl_prime_dq_i),
        .sync_out (w_wl_dq_sync)
    );

    assign w_wrlvl_ack_n = ~w_wl_ack_h_sync;
    assign w_rdlvl_req_n = ~w_rl_req_h_sync;
    assign w_wrlvl_dq_sync = w_wl_dq_sync;

endmodule : andesite_training_layer
