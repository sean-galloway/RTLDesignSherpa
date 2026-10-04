// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_wrlvl_ifc
// Purpose: wrlvl_ifc
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_wrlvl_ifc per andesite HAS ch02 (MODIFIED -- the andesite
// delta lands in a later P3 task; this file is the clean carried base).
//
// Author: sean galloway
// Created: 2026-10-04 (carried)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_wrlvl_ifc
    import andesite_pkg::*;
#(
    parameter int NUM_CS = 1,
    parameter int CSW    = (NUM_CS > 1) ? $clog2(NUM_CS) : 1
)(
    input  logic             mc_clk,
    input  logic             mc_rst_n,

    // ----- mode: the DRAM is in write-leveling mode iff MR1[7] is set.
    //       Driven from scoria_mode_register.wrlvl_en_o, which is the
    //       authority: JESD79-3F says the DRAM enters leveling mode when A7
    //       in MR1 is high and exits when it is low.
    input  logic             wrlvl_en_i,

    // ----- host controls (CSR) -----
    input  logic             strobe_i,        // pulse: emit ONE DQS edge
    input  logic [CSW-1:0]   cs_sel_i,        // which chip select to level
    input  logic [15:0]      t_wldqsen_i,     // 25 nCK min
    input  logic [15:0]      t_wlmrd_i,       // 40 nCK min
    input  logic [15:0]      t_wlmrd_max_i,   // OUR bound; 0 = no timeout
    input  logic [15:0]      t_wlo_i,         // result-return delay
    input  logic [15:0]      t_wloe_i,        // unused: prime bit only (Q3)

    // ----- DFI v3.1 per-CS leveling handshake -----
    output logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_o,
    input  logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_i,
    output logic [NUM_CS-1:0] dfi_phy_wrlvl_cs_n_o,   // selects WRITE leveling
    output logic              dfi_wrlvl_strobe_o,     // drive one DQS edge

    // ----- the DRAM's answer, on the prime DQ bit -----
    input  logic              prime_dq_i,

    // ----- telemetry -----
    output logic              result_valid_o,
    output logic              result_o,        // sampled prime DQ
    output logic [15:0]       obs_attempts_o,  // strobes emitted
    output logic [15:0]       obs_flips_o,     // result transitions seen
    output logic              obs_timeout_o,   // tWLMRD_max expired
    output logic              obs_ever_done_o, // a pass has completed
    output logic [2:0]        obs_state_o
);

    //=========================================================================
    // State. Enable-plus-strobe, so this is a window sequencer and not a search.
    //=========================================================================
    typedef enum logic [2:0] {
        WL_OFF     = 3'd0,  // not in leveling mode
        WL_DQSEN   = 3'd1,  // tWLDQSEN: before DQS may be driven
        WL_MRD     = 3'd2,  // tWLMRD: before the first DQS pulse
        WL_READY   = 3'd3,  // armed; waiting for a host strobe
        WL_WAIT_WLO= 3'd4,  // strobe sent; waiting tWLO for the answer
        WL_TIMEOUT = 3'd5   // tWLMRD_max expired without a usable result
    } wl_state_e;

    wl_state_e   r_state;
    logic [15:0] r_cnt;        // window countdown
    logic [15:0] r_since_mrd;  // elapsed since entering leveling, for the max
    logic [15:0] r_attempts;
    logic [15:0] r_flips;
    logic        r_result, r_result_valid, r_have_prev;
    logic        r_timeout, r_ever_done;

    logic w_max_armed;
    assign w_max_armed = (t_wlmrd_max_i != 16'd0);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state        <= WL_OFF;
            r_cnt          <= 16'd0;
            r_since_mrd    <= 16'd0;
            r_attempts     <= 16'd0;
            r_flips        <= 16'd0;
            r_result       <= 1'b0;
            r_result_valid <= 1'b0;
            r_have_prev    <= 1'b0;
            r_timeout      <= 1'b0;
            r_ever_done    <= 1'b0;
        end else if (!wrlvl_en_i) begin
            // MR1[7] cleared: the DRAM has left leveling mode. Counters and
            // the ever_done sticky survive -- they are the record of the pass
            // that just finished, and clearing them here would erase exactly
            // what the host reads afterwards.
            r_state        <= WL_OFF;
            r_result_valid <= 1'b0;
            r_have_prev    <= 1'b0;
        end else begin
            r_since_mrd <= r_since_mrd + 16'd1;

            unique case (r_state)
                WL_OFF: begin
                    // Just entered leveling mode.
                    r_state     <= WL_DQSEN;
                    r_cnt       <= t_wldqsen_i;
                    r_since_mrd <= 16'd0;
                    r_timeout   <= 1'b0;
                end

                WL_DQSEN: if (r_cnt == 16'd0) begin
                              r_state <= WL_MRD;
                              r_cnt   <= t_wlmrd_i;
                          end else r_cnt <= r_cnt - 16'd1;

                WL_MRD:   if (r_cnt == 16'd0) r_state <= WL_READY;
                          else                r_cnt   <= r_cnt - 16'd1;

                WL_READY: begin
                    if (strobe_i) begin
                        r_state    <= WL_WAIT_WLO;
                        r_cnt      <= t_wlo_i;
                        r_attempts <= r_attempts + 16'd1;
                        // RESTART the inactivity window on every accepted
                        // strobe. Without this, r_since_mrd measures total
                        // elapsed time since ENTERING leveling, while the
                        // timeout below is meant to mean "the host has stopped
                        // driving" -- and those diverge the moment the first
                        // strobe lands.
                        //
                        // The consequence was a spurious failure in the normal
                        // case: a host sweeping delay taps, each costing tWLO
                        // plus a UART round trip, blows through any sensible
                        // t_wlmrd_max part-way through and gets WL_TIMEOUT with
                        // obs_timeout set -- which reads as "leveling failed"
                        // on a pass that was working. Caught by
                        // test_scoria_wrlvl_ifc's sweep_does_not_spuriously_
                        // timeout at strobe 8 of 8, attempts 7.
                        r_since_mrd <= 16'd0;
                    end else if (w_max_armed && (r_since_mrd >= t_wlmrd_max_i)) begin
                        // Armed and not strobed for t_wlmrd_max: the host has
                        // stopped driving. Report it rather than waiting
                        // forever. t_wlmrd_max is OURS -- JESD79-3F declares
                        // tWLMRD's maximum controller-dependent.
                        r_state   <= WL_TIMEOUT;
                        r_timeout <= 1'b1;
                    end
                end

                WL_WAIT_WLO: begin
                    if (r_cnt == 16'd0) begin
                        // tWLO elapsed: the answer is on the prime DQ bit.
                        // tWLOE is NOT waited on -- it bounds mismatch ACROSS
                        // DQ bits and we sample one (HAS Q3).
                        r_result       <= prime_dq_i;
                        r_result_valid <= 1'b1;
                        r_ever_done    <= 1'b1;
                        if (r_have_prev && (prime_dq_i != r_result)) begin
                            r_flips <= r_flips + 16'd1;
                        end
                        r_have_prev <= 1'b1;
                        r_state     <= WL_READY;
                    end else begin
                        r_cnt <= r_cnt - 16'd1;
                    end
                end

                WL_TIMEOUT: begin
                    // Sticky until the host leaves leveling mode via MR1[7].
                    r_state <= WL_TIMEOUT;
                end

                default: r_state <= WL_OFF;
            endcase
        end
    end)

    //=========================================================================
    // Outputs -- every port is Q of a flop.
    //=========================================================================
    logic [NUM_CS-1:0] w_cs_onehot;
    always_comb begin
        w_cs_onehot = '0;
        // Guarded index. With NUM_CS = 1 the CSW floor makes cs_sel_i one bit
        // wide, so a host writing 1 would index past the vector. Verilator
        // does not flag a variable index out of range, so the guard is the
        // only thing standing between a stray CSR write and an X.
        if (cs_sel_i < CSW'(NUM_CS)) begin
            w_cs_onehot[cs_sel_i] = 1'b1;
        end
    end

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dfi_phylvl_req_cs_n_o <= '1;   // active LOW
            dfi_phy_wrlvl_cs_n_o  <= '1;
            dfi_wrlvl_strobe_o    <= 1'b0;
            result_valid_o        <= 1'b0;
            result_o              <= 1'b0;
            obs_attempts_o        <= 16'd0;
            obs_flips_o           <= 16'd0;
            obs_timeout_o         <= 1'b0;
            obs_ever_done_o       <= 1'b0;
            obs_state_o           <= 3'd0;
        end else begin
            // Request leveling on the selected CS for as long as the DRAM is
            // in leveling mode. Active low, hence the inversion.
            dfi_phylvl_req_cs_n_o <= wrlvl_en_i ? ~w_cs_onehot : '1;
            dfi_phy_wrlvl_cs_n_o  <= wrlvl_en_i ? ~w_cs_onehot : '1;
            // One-cycle DQS pulse, only once the windows have elapsed. A
            // strobe arriving early is DROPPED, not deferred: deferring it
            // would report an attempt the DRAM never saw.
            dfi_wrlvl_strobe_o    <= (r_state == WL_READY) && strobe_i;
            result_valid_o        <= r_result_valid;
            result_o              <= r_result;
            obs_attempts_o        <= r_attempts;
            obs_flips_o           <= r_flips;
            obs_timeout_o         <= r_timeout;
            obs_ever_done_o       <= r_ever_done;
            obs_state_o           <= r_state;
        end
    end)

endmodule : andesite_wrlvl_ifc
