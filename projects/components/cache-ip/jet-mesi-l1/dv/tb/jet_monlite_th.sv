// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_monlite_th
// Purpose:
//   Unit test harness for jet_monlite (Task 10, MAS ch04 J7 metrics):
//   exposes every tap input and the MonBus output at the top level, and
//   provides a simple functional-side counter that increments on alloc
//   pulses so the observer-transparency scenario can prove the observer
//   never stalls or perturbs the measured path.
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-29

`timescale 1ns / 1ps

module jet_monlite_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int MSHR_COUNT  = jet_pkg::MSHR_COUNT,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter bit USE_MONITOR = 1'b1,
    localparam int SET_W      = $clog2(SETS),
    localparam int WAY_W      = $clog2(WAYS),
    localparam int MW         = $clog2(MSHR_COUNT),
    localparam int OCC_W      = MW + 1
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ---- MSHR event taps ----
    input  logic                        mshr_alloc_i,
    input  logic [SET_W-1:0]            mshr_alloc_set_i,
    input  logic [1:0]                  mshr_alloc_cls_i,
    input  logic [MW-1:0]               mshr_alloc_idx_i,
    input  logic                        mshr_merge_i,
    input  logic [MW-1:0]               mshr_merge_idx_i,
    input  logic [MW:0]                 mshr_merge_depth_i,
    input  logic                        mshr_retire_i,
    input  logic [MW-1:0]               mshr_retire_idx_i,
    input  logic [OCC_W-1:0]            mshr_occupancy_i,

    // ---- WB event taps ----
    input  logic [$clog2(jet_pkg::VICTIM_DEPTH + 1)-1:0] wb_occupancy_i,

    // ---- control stall taps ----
    input  logic                        ctrl_stall_i,
    input  logic [2:0]                  ctrl_stall_reason_i,

    // ---- side-band timestamp ----
    input  logic [63:0]                 mon_time,

    // ---- MonBus observation stream ----
    output logic                        monbus_valid,
    input  logic                        monbus_ready,
    output logic [127:0]                monbus_packet,
    output logic [63:0]                 monbus_timestamp,
    output logic [7:0]                  monbus_dropped,

    // ---- functional-side reference (never touched by the observer) ----
    output logic [31:0]                 functional_count
);

    jet_monlite #(
        .MSHR_COUNT  (MSHR_COUNT),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .USE_MONITOR (USE_MONITOR)
    ) u_monlite (
        .clk                 (clk),
        .rst_n               (rst_n),
        .mshr_alloc_i        (mshr_alloc_i),
        .mshr_alloc_set_i    (mshr_alloc_set_i),
        .mshr_alloc_cls_i    (mshr_alloc_cls_i),
        .mshr_alloc_idx_i    (mshr_alloc_idx_i),
        .mshr_merge_i        (mshr_merge_i),
        .mshr_merge_idx_i    (mshr_merge_idx_i),
        .mshr_merge_depth_i  (mshr_merge_depth_i),
        .mshr_retire_i       (mshr_retire_i),
        .mshr_retire_idx_i   (mshr_retire_idx_i),
        .mshr_occupancy_i    (mshr_occupancy_i),
        .wb_occupancy_i      (wb_occupancy_i),
        .ctrl_stall_i        (ctrl_stall_i),
        .ctrl_stall_reason_i (ctrl_stall_reason_i),
        .i_mon_time          (mon_time),
        .monbus_valid        (monbus_valid),
        .monbus_ready        (monbus_ready),
        .monbus_packet       (monbus_packet),
        .monbus_timestamp    (monbus_timestamp),
        .dropped_count       (monbus_dropped)
    );

    // A simple functional path: counts alloc pulses.  The observer is
    // read-only; this counter must be identical whether USE_MONITOR is 0
    // or 1 and regardless of monbus_ready backpressure.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            functional_count <= 32'd0;
        end else if (mshr_alloc_i) begin
            functional_count <= functional_count + 32'd1;
        end
    )

endmodule : jet_monlite_th
