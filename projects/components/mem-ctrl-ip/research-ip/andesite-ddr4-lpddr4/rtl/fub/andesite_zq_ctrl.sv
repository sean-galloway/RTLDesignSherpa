// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_zq_ctrl
// Purpose: zq_ctrl
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_zq_ctrl per andesite HAS ch02 (MODIFIED -- the andesite
// LPDDR4 MPC delta is marked ANDESITE MPC DELTA: a memtype-selected sibling
// path hands the shared interval expiry to the andesite_zq_mpc_lpddr4
// submodule; the inherited DDR4 core is bit-identical when it is not
// selected).
//
// Author: sean galloway
// Created: 2026-10-04 (carried)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_zq_ctrl
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
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

    // ----- ANDESITE MPC DELTA: LPDDR4 calibration path -----
    // memtype selects the calibration path per MAS 07: the inherited core
    // below is the DDR4 path; MEMTYPE_LPDDR4 hands expiries to the MPC
    // submodule and muxes its request/grant onto this pair.
    input  memtype_e    memtype_i,
    input  logic [15:0] t_zq_i,             // tZQ latency, runtime CSR
    input  logic [5:0]  mpc_opcode_i,       // opcode IMAGE; encodings TBC(JESD209-4)
    // Protocol-facing submodule outputs, surfaced for the formatter's CA
    // path (consumed when the formatter integration lands).
    output logic        mpc_issuing_o,
    output logic [5:0]  mpc_op_o,

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

    // ----- ANDESITE MPC DELTA: LPDDR4 sibling path -----
    // memtype selects the calibration path (MAS 07). The inherited core
    // keeps owning the shared interval counter and the issued total; in
    // LPDDR4 mode it hands each expiry to the submodule, which owns the
    // scheduler handshake, and the shared interval reloads on its done.
    logic w_lpddr4;
    assign w_lpddr4 = (memtype_i == MEMTYPE_LPDDR4);

    logic        w_mpc_req, w_mpc_busy, w_mpc_done;

    andesite_zq_mpc_lpddr4 u_mpc (
        .mc_clk       (mc_clk),
        .mc_rst_n     (mc_rst_n),
        .enable_i     (w_run && w_lpddr4),
        .start_i      ((r_state == ZQ_IDLE) && (r_interval == 32'd0)),
        .t_zq_i       (t_zq_i),
        .mpc_opcode_i (mpc_opcode_i),
        .zq_req_o     (w_mpc_req),
        .zq_grant_i   (zq_grant_i),
        .mpc_issuing_o(mpc_issuing_o),
        .mpc_op_o     (mpc_op_o),
        .busy_o       (w_mpc_busy),
        .done_o       (w_mpc_done)
    );

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
                    if (w_mpc_done) begin
                        // ANDESITE MPC DELTA: the LPDDR4 calibration
                        // completed; reload the shared interval and count it
                        // in the shared total. (Inert in DDR4 mode: the
                        // submodule is parked and done_o never rises.)
                        r_interval <= t_zqcs_interval_i;
                        r_total    <= r_total + 16'd1;
                    end else if (r_interval == 32'd0) begin
                        if (!w_lpddr4) begin
                            // Mode C: defer under demand when placement == 1.
                            if (placement_i == 2'd1 && demand_i) begin
                                r_state     <= ZQ_DEFER;
                                r_defer_cnt <= 13'd0;
                                r_overdue   <= 1'b0;
                            end else begin
                                r_state   <= ZQ_REQ;
                                r_overdue <= 1'b0;
                            end
                        end
                        // ANDESITE MPC DELTA: LPDDR4 hands the expiry to the
                        // submodule (its start_i is the level condition this
                        // branch sees); the core stays in ZQ_IDLE and the
                        // interval reloads on w_mpc_done above.
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
    // Outputs. The family convention holds -- every observable is Q of a
    // flop; the ANDESITE MPC DELTA memtype mux is a combinational
    // passthrough of the two registered sources, so the LPDDR4 path keeps
    // the submodule's single-register latency and the DDR4 core's
    // observables stay bit-identical.
    //=========================================================================
    logic r_zq_req, r_obs_busy;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_zq_req           <= 1'b0;
            r_obs_busy         <= 1'b0;
            obs_zqcs_total_o   <= 16'd0;
            obs_interval_cnt_o <= 32'd0;
            obs_overdue_o      <= 1'b0;
        end else begin
            r_zq_req           <= (r_state == ZQ_REQ);
            r_obs_busy         <= (r_state == ZQ_HOLD);
            obs_zqcs_total_o   <= r_total;
            obs_interval_cnt_o <= r_interval;
            obs_overdue_o      <= r_overdue;
        end
    end)

    assign zq_req_o   = w_lpddr4 ? w_mpc_req  : r_zq_req;
    assign obs_busy_o = w_lpddr4 ? w_mpc_busy : r_obs_busy;

endmodule : andesite_zq_ctrl
