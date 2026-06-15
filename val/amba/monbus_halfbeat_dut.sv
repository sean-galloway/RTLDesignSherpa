// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: monbus_halfbeat_dut
// Purpose: Cosim harness — monbus_compressor (HALF_BEAT_EN=1) feeding
//          monbus_halfbeat_packer, i.e. the exact composition the
//          monbus_group_core uses when HALF_BEAT_EN=1. Exposes the same
//          record-in / slot-out interface as monbus_compressor so the
//          acceptance test can cross-check against the Python golden
//          Encoder(half_beat=True).

`timescale 1ns / 1ps

module monbus_halfbeat_dut
    import monitor_common_pkg::*;
(
    input  logic                clk,
    input  logic                rst_n,

    input  logic                in_valid,
    output logic                in_ready,
    input  monitor_packet_t     in_packet,
    input  monbus_timestamp_t   in_source_ts,

    output logic                out_valid,
    input  logic                out_ready,
    output logic [63:0]         out_slot,

    output logic [31:0]         stat_tier1_a,
    output logic [31:0]         stat_tier1_b,
    output logic [31:0]         stat_tier1_c,
    output logic [31:0]         stat_tier0,
    output logic [31:0]         stat_cam_miss,
    output logic [31:0]         stat_delta_ts_ovf,
    output logic [31:0]         stat_event_data_ovf,
    output logic [31:0]         stat_ed_delta_ovf
);

    logic        c_out_valid;
    logic        c_out_ready;
    logic [63:0] c_out_slot;
    logic        c_half_valid;
    logic [29:0] c_half_slot;

    monbus_compressor #(.HALF_BEAT_EN(1)) u_compressor (
        .clk                 (clk),
        .rst_n               (rst_n),
        .in_valid            (in_valid),
        .in_ready            (in_ready),
        .in_packet           (in_packet),
        .in_source_ts        (in_source_ts),
        .out_valid           (c_out_valid),
        .out_ready           (c_out_ready),
        .out_slot            (c_out_slot),
        .out_half_valid      (c_half_valid),
        .out_half_slot       (c_half_slot),
        .stat_tier1_a        (stat_tier1_a),
        .stat_tier1_b        (stat_tier1_b),
        .stat_tier1_c        (stat_tier1_c),
        .stat_tier0          (stat_tier0),
        .stat_cam_miss       (stat_cam_miss),
        .stat_delta_ts_ovf   (stat_delta_ts_ovf),
        .stat_event_data_ovf (stat_event_data_ovf),
        .stat_ed_delta_ovf   (stat_ed_delta_ovf)
    );

    monbus_halfbeat_packer u_packer (
        .clk           (clk),
        .rst_n         (rst_n),
        .in_valid      (c_out_valid),
        .in_ready      (c_out_ready),
        .in_slot       (c_out_slot),
        .in_half_valid (c_half_valid),
        .in_half_slot  (c_half_slot),
        .out_valid     (out_valid),
        .out_ready     (out_ready),
        .out_slot      (out_slot)
    );

endmodule : monbus_halfbeat_dut
