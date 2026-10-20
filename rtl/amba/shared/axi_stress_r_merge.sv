// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_r_merge
// Purpose: The read data channel of a bus-stress slave that answers AXI5
//          read-return atomics: the read core's R and the write core's atomic
//          R merged onto one R channel.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// A read-return atomic (AWATOP[5]) arrives on AW but answers on R with the
// AW's ID (AXI5). The write core makes that one R beat; this block puts it on
// the slave's R channel beside the read core's beats.
//
// The switch happens only between bursts: once a read burst has started it
// keeps the channel to its RLAST. An atomic beat is a burst of one, so it
// never splits a read burst -- a slave port whose read tracker expects
// bursts in order (no R interleaving) sees whole bursts either way. Between
// bursts the two sources alternate when both wait, so neither starves. A
// beat once presented stays selected until it is taken: AXI does not let
// VALID's payload change before READY. Purely combinational on the data
// path; three flags are the only state.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_r_merge #(
    parameter int IW = 8,
    parameter int DW = 64,
    parameter int XW = 8           // extra per-beat fields carried with R
) (
    input  logic          aclk,
    input  logic          aresetn,

    // the read core's R
    input  logic          a_valid,
    output logic          a_ready,
    input  logic [IW-1:0] a_id,
    input  logic [DW-1:0] a_data,
    input  logic [1:0]    a_resp,
    input  logic          a_last,
    input  logic [XW-1:0] a_x,

    // the write core's atomic R (always a single, last beat)
    input  logic          b_valid,
    output logic          b_ready,
    input  logic [IW-1:0] b_id,
    input  logic [DW-1:0] b_data,
    input  logic [1:0]    b_resp,
    input  logic [XW-1:0] b_x,

    // to the R channel module
    output logic          m_valid,
    input  logic          m_ready,
    output logic [IW-1:0] m_id,
    output logic [DW-1:0] m_data,
    output logic [1:0]    m_resp,
    output logic          m_last,
    output logic [XW-1:0] m_x
);

    logic r_in_burst;     // a read burst has started and not reached RLAST
    logic r_b_turn;       // between bursts, the atomic goes first next time
    logic r_held, r_held_b;   // a beat was presented and not taken: keep it

    logic w_sel_b;
    assign w_sel_b = r_held ? r_held_b
                   : (!r_in_burst && b_valid && (r_b_turn || !a_valid));

    assign m_valid = w_sel_b ? b_valid : a_valid;
    assign m_id    = w_sel_b ? b_id    : a_id;
    assign m_data  = w_sel_b ? b_data  : a_data;
    assign m_resp  = w_sel_b ? b_resp  : a_resp;
    assign m_last  = w_sel_b ? 1'b1    : a_last;
    assign m_x     = w_sel_b ? b_x     : a_x;
    assign a_ready = !w_sel_b && m_ready;
    assign b_ready =  w_sel_b && m_ready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_in_burst <= 1'b0;
            r_b_turn   <= 1'b0;
            r_held     <= 1'b0;
            r_held_b   <= 1'b0;
        end else begin
            r_held   <= m_valid && !m_ready;
            r_held_b <= w_sel_b;
            if (a_valid && a_ready) begin
                r_in_burst <= !a_last;
                if (a_last) r_b_turn <= 1'b1;
            end
            if (b_valid && b_ready) r_b_turn <= 1'b0;
        end
    )

endmodule : axi_stress_r_merge
