// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scoria_zq_ctrl
// Purpose: Periodic ZQ calibration (ZQCS) as MAINTENANCE TRAFFIC.
//
//          NEW in scoria -- DDR2 has no ZQ calibration, so pumice has no
//          counterpart. See scoria_has ch03_architecture/02_init_zq.md.
//
//          ZQCL at initialization belongs to the init sequencer. This module
//          owns the PERIODIC short calibration, and it is a scheduling problem
//          rather than a sequencing one: the controller must issue ZQCS on an
//          interval no host asked for, competing with demand traffic for the
//          command bus. That is the same shape as refresh, so this module
//          presents the same REQUEST/GRANT interface refresh_ctrl does, and
//          the arbiter sees one kind of maintenance demand with a source tag
//          rather than two special cases.
//
//          IT NEVER PREEMPTS. It raises zq_req_o and waits. This is not a
//          conservative guess -- it is what two independent controllers do:
//          LiteDRAM's DDR3 core starts its ZQCS executer from inside the
//          refresher FSM and drives refresh_req to every bank machine, which
//          must grant before the command issues; pumice's refresh does the
//          same. See scoria_has ch06 Q2.
//
//          tZQCS is enforced by holding off the NEXT interval, not by blocking
//          traffic: once the command is granted the bus is released and the
//          reload simply starts later. LiteDRAM does the same thing with its
//          zqcs_timer_wait.
//
// v2 (TASK-001 Mode C): ZQCS placement policy.
//   placement_i[1:0]: 0 = request on expiry (bit-identical to v1), 1 = defer
//   under sustained demand, 2 reserved.  overdue_max_i[12:0] caps the deferral
//   (0 = no cap).  When placement_i == 1 and demand_i is high at interval
//   expiry the FSM enters ZQ_DEFER; it exits to ZQ_REQ when demand drops,
//   placement is changed back to 0, or the overdue limit is reached.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scoria_zq_ctrl
    import scoria_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    // ----- configuration; runtime CSRs, like every enforced timing here -----
    input  logic        enable_i,           // 0 = never issue ZQCS
    input  logic [31:0] t_zqcs_interval_i,  // MC cycles between calibrations.
                                            // Needs 32 bits: a ~128 ms interval
                                            // at 100 MHz is ~12.8M cycles, which
                                            // does not fit the 16 bits tREFI uses.
    input  logic [15:0] t_zqcs_i,           // tZQCS, max(64 nCK, 80 ns) for
                                            // MT41J256M16; held after a grant

    // Mode C: ZQCS placement policy
    input  logic [1:0]  placement_i,        // 0 = request on expiry (v1)
    input  logic [12:0] overdue_max_i,      // max deferral cycles (0 = none)

    // ----- arbiter interface: identical in shape to refresh_ctrl's -----
    input  logic        demand_i,           // scheduler has read/write work
    output logic        zq_req_o,
    input  logic        zq_grant_i,

    // ----- telemetry. NOT optional: the interval must be confirmable from
    //       the host, or "ZQCS is being issued" is an assumption. scoria_has
    //       ch06 Q2 names the starvation check this enables.
    output logic        obs_busy_o,         // in the post-grant tZQCS window
    output logic [15:0] obs_zqcs_total_o,   // calibrations issued since reset
    output logic [31:0] obs_interval_cnt_o, // live countdown, for host sanity
    output logic        obs_overdue_o       // interval expired, still no grant
);

    //=========================================================================
    // State
    //=========================================================================
    typedef enum logic [1:0] {
        ZQ_IDLE  = 2'd0,   // counting down to the next calibration
        ZQ_REQ   = 2'd1,   // asking the arbiter, waiting for a grant
        ZQ_HOLD  = 2'd2,   // granted; holding tZQCS before reloading
        ZQ_DEFER = 2'd3    // Mode C: interval expired, demand high, deferring
    } zq_state_e;

    zq_state_e   r_state;
    logic [31:0] r_interval;
    logic [15:0] r_hold;
    logic [15:0] r_total;
    logic        r_overdue;
    logic [12:0] r_defer_cnt;   // Mode C: cycles spent in ZQ_DEFER

    // An interval of 0 would otherwise reload to 0 and request every cycle.
    // Treat it as "disabled" rather than "as fast as possible".
    logic w_interval_valid;
    assign w_interval_valid = (t_zqcs_interval_i != 32'd0);

    logic w_run;
    assign w_run = enable_i && w_interval_valid;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state    <= ZQ_IDLE;
            // Seeded from the INPUT, not zero. ZQ_IDLE treats r_interval == 0
            // as "fire now", so a zero reset makes the first interval
            // zero-length and a calibration is issued immediately out of
            // reset -- along with a spurious obs_overdue_o if demand is up.
            //
            // LATENT rather than live in the assembled design: ZQ_CFG.zq_enable
            // resets to 0 and the scheduler additionally gates enable_i on
            // init_done, so w_run is false out of reset and the !w_run branch
            // below reloads from the input before anything can fire. But that
            // makes this module's correctness depend on two other modules'
            // reset values, which is the kind of coupling that breaks quietly
            // when one of them changes. Found by test_scoria_zq_ctrl's
            // overdue_needs_demand_and_expiry, which holds enable high through
            // reset -- a configuration the CSRs cannot currently produce and
            // a unit test can.
            r_interval   <= t_zqcs_interval_i;
            r_hold       <= 16'd0;
            r_total      <= 16'd0;
            r_overdue    <= 1'b0;
            r_defer_cnt  <= 13'd0;
        end else if (!w_run) begin
            // Disabled: park, and reload so enabling does not fire instantly.
            r_state     <= ZQ_IDLE;
            r_interval  <= t_zqcs_interval_i;
            r_overdue   <= 1'b0;
            r_defer_cnt <= 13'd0;
        end else begin
            unique case (r_state)
                ZQ_IDLE: begin
                    if (r_interval == 32'd0) begin
                        // Mode C: defer under demand when placement == 1.
                        if (placement_i == 2'd1 && demand_i) begin
                            r_state     <= ZQ_DEFER;
                            r_defer_cnt <= 13'd0;
                            r_overdue   <= 1'b0;
                        end else begin
                            r_state   <= ZQ_REQ;
                            r_overdue <= 1'b0;
                        end
                    end else begin
                        r_interval <= r_interval - 32'd1;
                    end
                end

                ZQ_REQ: begin
                    // Waiting on the arbiter. The interval has already
                    // expired, so any further wait is the scheduler holding
                    // us off -- which is exactly what obs_overdue_o reports.
                    // demand_i is not gated on here: a request that withdrew
                    // itself under load would starve silently, which is the
                    // failure mode the telemetry exists to make visible.
                    if (zq_grant_i) begin
                        r_state <= ZQ_HOLD;
                        r_hold  <= t_zqcs_i;
                        r_total <= r_total + 16'd1;
                    end else if (demand_i) begin
                        r_overdue <= 1'b1;
                    end
                end

                ZQ_HOLD: begin
                    if (r_hold == 16'd0) begin
                        r_state    <= ZQ_IDLE;
                        r_interval <= t_zqcs_interval_i;
                    end else begin
                        r_hold <= r_hold - 16'd1;
                    end
                end

                ZQ_DEFER: begin
                    // Hold the request under demand.  Exit on loss of demand,
                    // policy change, or overdue limit.  obs_overdue_o is raised
                    // while we are intentionally deferred (starvation telemetry).
                    if (placement_i != 2'd1 || !demand_i) begin
                        r_state     <= ZQ_REQ;
                        r_defer_cnt <= 13'd0;
                    end else if (overdue_max_i != 13'd0 &&
                                 r_defer_cnt >= overdue_max_i) begin
                        r_state     <= ZQ_REQ;
                        r_defer_cnt <= 13'd0;
                    end else begin
                        r_defer_cnt <= r_defer_cnt + 13'd1;
                    end
                    r_overdue <= 1'b1;
                end

                default: r_state <= ZQ_IDLE;
            endcase
        end
    end)

    //=========================================================================
    // Outputs -- every port is Q of a flop, per the family convention.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            zq_req_o           <= 1'b0;
            obs_busy_o         <= 1'b0;
            obs_zqcs_total_o   <= 16'd0;
            obs_interval_cnt_o <= 32'd0;
            obs_overdue_o      <= 1'b0;
        end else begin
            zq_req_o           <= (r_state == ZQ_REQ);
            obs_busy_o         <= (r_state == ZQ_HOLD);
            obs_zqcs_total_o   <= r_total;
            obs_interval_cnt_o <= r_interval;
            obs_overdue_o      <= r_overdue;
        end
    end)

endmodule : scoria_zq_ctrl
