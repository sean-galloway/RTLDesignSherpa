// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: powerdown_ctrl
// Purpose: Idle-detect → CKE-low precharge power-down.
//
//          When `controller_idle_i` stays high continuously for
//          `idle_threshold_i` MC cycles AND `enable_pde_i` is asserted,
//          raise `pdn_req_o`. The scheduler grants by pulsing
//          `pdn_grant_i` once it's safe (no pending DRAM commands).
//          On grant, drive `dfi_cke_o` low. As soon as
//          `controller_idle_i` drops again, drive CKE high to wake.
//
// v2 status (LPDDR2 enable framework):
//   * Adds `enable_dpd_i` parameter as a placeholder for LPDDR2 Deep
//     Power Down. The actual DPD entry sequence (which involves driving
//     CKE low along with a specific MR write per JESD209-2 §5.5) is a
//     v3 task once the CSR slave provides per-rank programming.
//
// v3 TODO:
//   * Self-refresh entry (`enable_sref_i`) — requires PRE-ALL first
//     and an S_SR state. Today only CKE-low PDE is implemented.
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
    input  logic                 enable_sref_i,       // v2 framework: ignored

    input  logic                 controller_idle_i,   // from scheduler

    output logic                 pdn_req_o,
    input  logic                 pdn_grant_i,

    output logic [CS_WIDTH-1:0]  dfi_cke_o
);

    //=========================================================================
    // FSM states
    //=========================================================================
    typedef enum logic [1:0] {
        S_AWAKE     = 2'd0,   // CKE high, normal operation
        S_ARMING    = 2'd1,   // counting idle cycles toward PDE
        S_REQ       = 2'd2,   // pdn_req high, awaiting grant
        S_ASLEEP    = 2'd3    // CKE low, powered down
    } state_e;

    state_e         r_state;
    logic [15:0]    r_idle_cnt;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state    <= S_AWAKE;
            r_idle_cnt <= 16'd0;
        end else begin
            unique case (r_state)
                S_AWAKE: begin
                    r_idle_cnt <= 16'd0;
                    if (enable_pde_i && controller_idle_i) begin
                        r_state <= S_ARMING;
                    end
                end

                S_ARMING: begin
                    if (!controller_idle_i || !enable_pde_i) begin
                        r_state    <= S_AWAKE;
                        r_idle_cnt <= 16'd0;
                    end else if (r_idle_cnt >= idle_threshold_i) begin
                        r_state <= S_REQ;
                    end else begin
                        r_idle_cnt <= r_idle_cnt + 16'd1;
                    end
                end

                S_REQ: begin
                    if (!controller_idle_i || !enable_pde_i) begin
                        // Activity arrived; back off the PDE request.
                        r_state    <= S_AWAKE;
                        r_idle_cnt <= 16'd0;
                    end else if (pdn_grant_i) begin
                        r_state <= S_ASLEEP;
                    end
                end

                S_ASLEEP: begin
                    // Wake on any new activity.
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
            pdn_req_o <= 1'b0;
            dfi_cke_o <= '1;             // CKE high out of reset
        end else begin
            pdn_req_o <= (r_state == S_REQ);
            dfi_cke_o <= (r_state == S_ASLEEP) ? '0 : '1;
        end
    end)

    wire unused_v1 = |{ enable_sref_i };

endmodule : powerdown_ctrl
