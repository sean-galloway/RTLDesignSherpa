// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_zq_mpc_lpddr4
// Purpose: LPDDR4 MPC ZQ-calibration sequencer (andesite zq_ctrl submodule)
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// New for andesite per andesite_mas ch02_blocks/07_zq_ctrl.md: LPDDR4 carries
// calibration on the MPC command, so this submodule sequences it through the
// formatter's LPDDR4 CA path while the inherited zq_ctrl core keeps owning
// the shared interval counter and the issued-total telemetry.
//
// Author: sean galloway
// Created: 2026-10-04 (andesite MPC submodule)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_zq_mpc_lpddr4
    import andesite_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    // memtype-gated by the parent: high only when the LPDDR4 path is
    // selected AND the parent core is running. Parked (disabled) otherwise.
    input  logic        enable_i,
    // The shared interval expired (level): the parent core stays in its
    // IDLE state and hands the expiry here; the shared interval reloads on
    // done_o, so a level start cannot re-trigger before the reload lands.
    input  logic        start_i,
    // tZQ, the LPDDR4 ZQ-calibration latency, runtime CSR (JESD209-4
    // speed-bin derived at CSR-derivation time).
    input  logic [15:0] t_zq_i,
    // MPC opcode IMAGE from the CSR. The encodings are TBC(JESD209-4): this
    // block drives the image at the protocol level and never decodes it --
    // no MPC opcode encodings are invented anywhere in andesite.
    input  logic [5:0]  mpc_opcode_i,

    // scheduler request/grant, muxed with the inherited core's pair by the
    // parent. Request-and-wait, never preempts: the request holds until its
    // one-cycle grant arrives.
    output logic        zq_req_o,
    input  logic        zq_grant_i,

    // Protocol-facing outputs. The formatter samples the opcode image WITH
    // the grant cycle, so these follow the FSM state combinationally; the
    // OP_MPC command identity rides the command stream separately.
    output logic        mpc_issuing_o,   // state == MPC_ISSUE
    output logic [5:0]  mpc_op_o,        // the image, presented while issuing

    output logic        busy_o,          // in the calibration window (WAIT)
    output logic        done_o           // 1-cycle: complete; reload interval
);

    // MAS 07 fence:
    //   MPC_IDLE -> MPC_ISSUE (assert cmd_req, wait for scheduler grant,
    //                drive MPC ZQCal start)
    //            -> MPC_WAIT   (wait tZQ latched from CSR)
    //            -> MPC_DONE   (drive calibration complete, reload interval)
    //            -> MPC_IDLE
    typedef enum logic [1:0] {
        MPC_IDLE  = 2'd0,
        MPC_ISSUE = 2'd1,
        MPC_WAIT  = 2'd2,
        MPC_DONE  = 2'd3
    } mpc_state_e;

    mpc_state_e  r_state;
    logic [15:0] r_wait;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state  <= MPC_IDLE;
            r_wait   <= 16'd0;
            zq_req_o <= 1'b0;
            busy_o   <= 1'b0;
            done_o   <= 1'b0;
        end else if (!enable_i) begin
            // Parked: no path selected, or the parent core is down.
            r_state  <= MPC_IDLE;
            zq_req_o <= 1'b0;
            busy_o   <= 1'b0;
            done_o   <= 1'b0;
        end else begin
            zq_req_o <= 1'b0;
            done_o   <= 1'b0;
            unique case (r_state)
                MPC_IDLE: begin
                    busy_o <= 1'b0;
                    if (start_i) begin
                        r_state <= MPC_ISSUE;
                    end
                end

                MPC_ISSUE: begin
                    zq_req_o <= 1'b1;
                    if (zq_grant_i) begin
                        r_state <= MPC_WAIT;
                        r_wait  <= t_zq_i;
                        busy_o  <= 1'b1;
                    end
                end

                MPC_WAIT: begin
                    busy_o <= 1'b1;
                    if (r_wait == 16'd0) begin
                        r_state <= MPC_DONE;
                        busy_o  <= 1'b0;
                    end else begin
                        r_wait <= r_wait - 16'd1;
                    end
                end

                MPC_DONE: begin
                    done_o  <= 1'b1;
                    r_state <= MPC_IDLE;
                end

                default: r_state <= MPC_IDLE;
            endcase
        end
    end)

    // Combinational protocol-facing outputs: the formatter's CA path samples
    // the image on the grant cycle, so these must not wait for a flop.
    assign mpc_issuing_o = (r_state == MPC_ISSUE);
    assign mpc_op_o      = mpc_opcode_i;

endmodule : andesite_zq_mpc_lpddr4
