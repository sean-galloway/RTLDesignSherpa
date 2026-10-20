// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_slot
// Purpose: build-infer's device under test for alu_harness: alu_infer_top,
//          in the profile this bitstream carries
//
// Documentation: projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/README.md
// Subsystem: fpga-systems / compute-eng-ip
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - PROFILE "LEAN": every EN_* off -- the v1 bf16 ALU, the first timing
//     number.  "FULL": the RTL defaults, every format and family built.
//   - slot_info reports what was built, so the host never has to be told.

`timescale 1ns / 1ps

module alu_slot #(
    parameter string PROFILE = "FULL"
) (
    input  logic        clk,
    input  logic        aresetn,
    input  logic [31:0] op_line_a,
    input  logic [31:0] op_line_b,
    input  logic [15:0] threshold_imm,
    input  logic [8:0]  func_sel,
    input  logic [1:0]  acc_ctrl,
    input  logic        valid,
    output logic        ready,
    output logic        result_valid,
    input  logic        result_ready,
    output logic [31:0] result_line,
    output logic [31:0] result_flags,
    output logic        err_opcode,
    output logic [31:0] slot_info
);

    localparam bit EN       = (PROFILE != "LEAN");
    localparam int PIPE_DEP = 8;
    localparam int ADD_LAT  = 3;
    localparam int MUL_LAT  = 0;
    localparam int MAC_LAT  = 0;

    initial begin
        if (PROFILE != "LEAN" && PROFILE != "FULL")
            $error("alu_slot: PROFILE must be \"LEAN\" or \"FULL\", got %s", PROFILE);
    end

    alu_infer_top #(
        .LINE_W        (32),
        .PIPE_DEPTH    (PIPE_DEP),
        .ADDER_LATENCY (ADD_LAT),
        .MUL_LATENCY   (MUL_LAT),
        .MAC_LATENCY   (MAC_LAT),
        .EN_INT8       (EN),
        .EN_FP32       (EN),
        .EN_FP8        (EN),
        .EN_REDUCE     (EN),
        .EN_PWL        (EN),
        .EN_ACT        (EN),
        .EN_CVT        (EN)
    ) u_alu (
        .clk           (clk),
        .aresetn       (aresetn),
        .op_line_a     (op_line_a),
        .op_line_b     (op_line_b),
        .threshold_imm (threshold_imm),
        .func_sel      (func_sel),
        .acc_ctrl      (acc_ctrl),
        .valid         (valid),
        .ready         (ready),
        .result_valid  (result_valid),
        .result_ready  (result_ready),
        .result_line   (result_line),
        .result_flags  (result_flags),
        .err_opcode    (err_opcode)
    );

    // {pipe_depth[28:24], mac_lat[22:20], mul_lat[18:16], add_lat[14:12],
    //  en[10:4] = CVT ACT PWL REDUCE FP8 FP32 INT8, kind[3:0] = 1 alu-infer}
    assign slot_info = {3'd0, 5'(PIPE_DEP), 1'b0, 3'(MAC_LAT), 1'b0, 3'(MUL_LAT),
                        1'b0, 3'(ADD_LAT), 1'b0, {7{EN}}, 4'd1};

endmodule : alu_slot
