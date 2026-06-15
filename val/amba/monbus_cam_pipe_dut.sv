// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: monbus_cam_pipe_dut
// Purpose: Equivalence harness — drives the single-cycle monbus_cam (reference)
//          and the 2-cycle monbus_cam_pipe with the SAME access stream and the
//          SAME action (action derived from the reference's combinational hit:
//          TOUCH on hit, INSTALL on miss, NONE when idle). The test compares
//          the pipelined result sequence (1-cycle delayed) against the
//          reference result sequence; they must be identical.

`timescale 1ns / 1ps

module monbus_cam_pipe_dut #(
    parameter int KEY_WIDTH  = 49,
    parameter int DATA_WIDTH = 64,
    parameter int TS_WIDTH   = 24,
    parameter int DEPTH      = 32,
    parameter int IDX_WIDTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1,
    parameter int CNT_WIDTH  = $clog2(DEPTH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    input  logic                    en,
    input  logic [KEY_WIDTH-1:0]    key,
    input  logic [DATA_WIDTH-1:0]   new_data,
    input  logic [TS_WIDTH-1:0]     new_ts,

    // reference (single-cycle, combinational this cycle)
    output logic                    ref_hit,
    output logic [IDX_WIDTH-1:0]    ref_idx,
    output logic [DATA_WIDTH-1:0]   ref_old_data,
    output logic [TS_WIDTH-1:0]     ref_old_ts,

    // pipelined (registered, valid next cycle)
    output logic                    pipe_valid,
    output logic                    pipe_hit,
    output logic [IDX_WIDTH-1:0]    pipe_idx,
    output logic [DATA_WIDTH-1:0]   pipe_old_data,
    output logic [TS_WIDTH-1:0]     pipe_old_ts
);
    localparam logic [1:0] ACTION_NONE    = 2'b00;
    localparam logic [1:0] ACTION_TOUCH   = 2'b01;
    localparam logic [1:0] ACTION_INSTALL = 2'b10;

    // Shared action: derived from the reference's combinational hit so both
    // CAMs evolve identically. (Mirrors the compressor: TOUCH on hit else INSTALL.)
    logic [1:0] action;
    assign action = !en ? ACTION_NONE : (ref_hit ? ACTION_TOUCH : ACTION_INSTALL);

    monbus_cam #(
        .KEY_WIDTH(KEY_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .TS_WIDTH(TS_WIDTH), .DEPTH(DEPTH)
    ) u_ref (
        .clk(clk), .rst_n(rst_n),
        .access_key(key), .access_hit(ref_hit), .access_idx(ref_idx),
        .access_old_data(ref_old_data), .access_old_ts(ref_old_ts),
        .access_action(action), .access_new_data(new_data), .access_new_ts(new_ts),
        .cam_full(), .cam_count(), .evicted()
    );

    monbus_cam_pipe #(
        .KEY_WIDTH(KEY_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .TS_WIDTH(TS_WIDTH), .DEPTH(DEPTH)
    ) u_pipe (
        .clk(clk), .rst_n(rst_n),
        .access_en(en), .access_key(key),
        .access_new_data(new_data), .access_new_ts(new_ts),
        .result_valid(pipe_valid), .result_hit(pipe_hit), .result_idx(pipe_idx),
        .result_old_data(pipe_old_data), .result_old_ts(pipe_old_ts),
        .cam_full(), .cam_count()
    );

endmodule : monbus_cam_pipe_dut
