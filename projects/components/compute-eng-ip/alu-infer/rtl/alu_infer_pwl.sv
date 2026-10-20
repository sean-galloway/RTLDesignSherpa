// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_pwl
// Purpose: 256-entry LUT piecewise-linear bf16 activation: y = slope*x + icpt
//          per lane, segment chosen from x's sign, octave and top mantissa bits
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - Entry = {slope bf16 [31:16], intercept bf16 [15:0]}.  Loaded through the
//     seam itself (OP_PWL_LUT sub_op 0: A = entry, B[7:0] = index), so the
//     table arrives in-band like everything else; sub_op 1 reads one back.
//   - Segment index = {sign, octave[3:0], mant[6:4]}: octave = exp - 120
//     clamped to [0,15], i.e. |x| in [2^-7, 2^9) at 8 segments per octave.
//     |x| < 2^-7 uses segment {sign,0,0}; |x| >= 2^9, inf and NaN use
//     {sign,15,7}.  The table generator fits each segment over that range.
//   - y = bf16(fma(slope, x, icpt)): one fp32 rounding then RNE to bf16.  An
//     infinite x against a zero slope returns the intercept (the saturating
//     tail), instead of the 0*inf NaN.
//   - The table is a memory: no reset (house SRAM rule); load it before use.

`timescale 1ns / 1ps

module alu_infer_pwl
    import alu_infer_pkg::*;
#(
    parameter int LINE_W = 32
) (
    input  logic              clk,

    input  logic              lut_we,
    input  logic [7:0]        lut_waddr,
    input  logic [31:0]       lut_wdata,
    input  logic [7:0]        lut_raddr,
    output logic [31:0]       lut_rdata,

    input  logic [LINE_W-1:0] a_line,
    output logic [LINE_W-1:0] o_line
);

    localparam int NL = LINE_W / 16;

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [31:0] r_lut [256];

    always_ff @(posedge clk) begin
        if (lut_we) r_lut[lut_waddr] <= lut_wdata;
    end

    assign lut_rdata = r_lut[lut_raddr];

    function automatic logic [7:0] seg_index(input logic [15:0] x);
        logic [7:0] e;
        e = x[14:7];
        if (e < 8'd120)      return {x[15], 4'd0, 3'd0};
        else if (e > 8'd135) return {x[15], 4'd15, 3'd7};
        else                 return {x[15], 4'(e - 8'd120), x[6:4]};
    endfunction

    generate
        for (genvar i = 0; i < NL; i++) begin : gen_lane
            logic [15:0] x, slope, icpt, y;
            logic [31:0] entry, f;
            logic        x_inf, slope_zero;

            assign x          = a_line[i*16 +: 16];
            assign entry      = r_lut[seg_index(x)];
            assign slope      = entry[31:16];
            assign icpt       = entry[15:0];
            assign x_inf      = (x[14:7] == 8'hFF) && (x[6:0] == 7'h0);
            assign slope_zero = (slope[14:0] == 15'h0);

            math_bf16_fma u_fma (
                .i_a        (slope),
                .i_b        (x),
                .i_c        ({icpt, 16'h0}),
                .ow_result  (f),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid ()
            );

            math_fp32_to_bf16 u_round (
                .i_a         (f),
                .ow_result   (y),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  ()
            );

            assign o_line[i*16 +: 16] = (x_inf && slope_zero) ? icpt : y;
        end
    endgenerate

endmodule : alu_infer_pwl
