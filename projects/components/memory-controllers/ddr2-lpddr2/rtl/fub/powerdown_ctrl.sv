// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: powerdown_ctrl
// Purpose: Idle-detect → low-power state. Two flavors:
//
//   1. PDE (Precharge Power Down)  — CKE low, banks may stay active.
//      Wakes on any new activity within ~tXPDLL cycles.
//   2. SR  (Self Refresh)          — CKE low + SRE command issued by
//      scheduler. DRAM self-refreshes internally; controller stops
//      issuing REFs. Exit requires SRX + tXSDLL (DDR2) / tXSR (LPDDR2)
//      before any new commands. SR entry requires all banks PRE first
//      (scheduler enforces precondition before granting).
//
// Selection (E v2):
//   * enable_sref_i high  → on idle threshold, request SR
//                           (pdn_kind_o = 1)
//   * enable_sref_i low,
//     enable_pde_i high   → on idle threshold, request PDE
//                           (pdn_kind_o = 0)
//   * neither              → never request
//
// v3 TODO:
//   * Deep Power Down entry (`enable_dpd_i`, LPDDR2 only) — needs
//     `dfi_dram_clk_disable_o` cooperation from dfi_signal_pack.
//   * Per-rank powerdown — currently powers down ALL ranks together.
//   * `dfi_init_complete` interlock — currently trusts the scheduler
//     to not grant before init completes.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module powerdown_ctrl
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int CS_WIDTH  = NUM_RANKS
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  logic [15:0]          idle_threshold_i,    // cycles
    input  logic                 enable_pde_i,
    input  logic                 enable_sref_i,       // takes priority over PDE

    input  logic                 controller_idle_i,   // from scheduler

    output logic                 pdn_req_o,
    output logic                 pdn_kind_o,          // 0=PDE, 1=SR
    input  logic                 pdn_grant_i,

    output logic                 sref_active_o,       // high while in SR

    output logic [CS_WIDTH-1:0]  dfi_cke_o,

    // obs_* (future CSR readout)
    output logic [2:0]           obs_state_o,
    output logic [15:0]          obs_idle_cnt_o,
    output logic [15:0]          obs_grants_pde_o,
    output logic [15:0]          obs_grants_sr_o
);

    //=========================================================================
    // FSM states
    //=========================================================================
    typedef enum logic [2:0] {
        S_AWAKE     = 3'd0,   // CKE high, normal operation
        S_ARMING    = 3'd1,   // counting idle cycles toward entry
        S_REQ       = 3'd2,   // pdn_req high, awaiting grant
        S_ASLEEP    = 3'd3    // CKE low, in PDE or SR (per r_kind)
    } state_e;

    state_e         r_state;
    logic [15:0]    r_idle_cnt;
    // 0 = PDE, 1 = SR. Latched when entering S_REQ.
    logic           r_kind;

    logic [15:0]    r_grants_pde;
    logic [15:0]    r_grants_sr;

    logic w_request_enabled;
    assign w_request_enabled = enable_pde_i || enable_sref_i;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state      <= S_AWAKE;
            r_idle_cnt   <= 16'd0;
            r_kind       <= 1'b0;
            r_grants_pde <= 16'd0;
            r_grants_sr  <= 16'd0;
        end else begin
            unique case (r_state)
                S_AWAKE: begin
                    r_idle_cnt <= 16'd0;
                    if (w_request_enabled && controller_idle_i) begin
                        r_state <= S_ARMING;
                    end
                end

                S_ARMING: begin
                    if (!controller_idle_i || !w_request_enabled) begin
                        r_state    <= S_AWAKE;
                        r_idle_cnt <= 16'd0;
                    end else if (r_idle_cnt >= idle_threshold_i) begin
                        r_state <= S_REQ;
                        // SR has priority over PDE when both enabled.
                        r_kind  <= enable_sref_i;
                    end else begin
                        r_idle_cnt <= r_idle_cnt + 16'd1;
                    end
                end

                S_REQ: begin
                    if (!controller_idle_i || !w_request_enabled) begin
                        // Activity arrived or both modes disabled — back off.
                        r_state    <= S_AWAKE;
                        r_idle_cnt <= 16'd0;
                    end else if (pdn_grant_i) begin
                        r_state <= S_ASLEEP;
                        if (r_kind) r_grants_sr  <= r_grants_sr  + 16'd1;
                        else        r_grants_pde <= r_grants_pde + 16'd1;
                    end
                end

                S_ASLEEP: begin
                    // Wake on any new activity. SR exit timing (tXSDLL/tXSR)
                    // is enforced by the scheduler — this FSM only drops CKE.
                    if (!controller_idle_i) begin
                        r_state    <= S_AWAKE;
                        r_idle_cnt <= 16'd0;
                    end
                end

                default: r_state <= S_AWAKE;
            endcase
        end
    end)

    // Strict-flop outputs.
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            pdn_req_o        <= 1'b0;
            pdn_kind_o       <= 1'b0;
            sref_active_o    <= 1'b0;
            dfi_cke_o        <= '1;             // CKE high out of reset
            obs_state_o      <= 3'd0;
            obs_idle_cnt_o   <= 16'd0;
            obs_grants_pde_o <= 16'd0;
            obs_grants_sr_o  <= 16'd0;
        end else begin
            pdn_req_o        <= (r_state == S_REQ);
            pdn_kind_o       <= r_kind;
            sref_active_o    <= (r_state == S_ASLEEP) && r_kind;
            dfi_cke_o        <= (r_state == S_ASLEEP) ? '0 : '1;
            obs_state_o      <= r_state;
            obs_idle_cnt_o   <= r_idle_cnt;
            obs_grants_pde_o <= r_grants_pde;
            obs_grants_sr_o  <= r_grants_sr;
        end
    end)

endmodule : powerdown_ctrl
