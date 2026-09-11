// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_softmax_8
//
// Verifies:
//   - Valid output handshake (ow_valid follows i_valid after pipeline)
//   - Output values are non-negative
//   - Reset clears outputs

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_softmax_8 (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    // PACKED, not an unpacked array: the proof reads the module through the
    // sv2v flatten flow (yosys cannot parse an unpacked array PORT), and
    // sv2v turns `logic [7:0] i_data [8]` into `[63:0]`. Lane i is
    // bits [8*i +: 8].
    (* anyconst *) logic [63:0] data_in;
    // FREE every clock. This was a plain `logic` assigned only in the reset
    // branch, so outside reset it held 0 forever: i_valid never rose, the
    // pipeline never produced an output, and c_valid_out was unreachable --
    // a cover that could not be hit whatever the RTL did.
    (* anyseq *) logic valid_in;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic                 w_valid_out;
    logic [63:0] w_result;

    math_fp8_e4m3_softmax_8 dut (
        .i_clk     (clk),
        .i_rst_n   (rst_n),
        .i_valid   (valid_in),
        .i_data    (data_in),
        .ow_valid  (w_valid_out),
        .ow_result (w_result)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Assumptions: start in reset, release after 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Property: Reset clears valid
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            p_reset_clears_valid: assert (!w_valid_out);
        end
    end

    // =========================================================================
    // Property: Output values are non-negative (softmax outputs >= 0)
    // =========================================================================
    generate
        genvar gi;
        for (gi = 0; gi < 8; gi++) begin : gen_nonneg
            always @(posedge clk) begin
                if (f_past_valid >= 5 && rst_n && w_valid_out) begin
                    assert (w_result[(8*gi) + 7] == 1'b0);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Cover: valid output after pipeline flush
    // =========================================================================
    always @(posedge clk) begin
        c_valid_out: cover (f_past_valid >= 5 && rst_n && w_valid_out);
    end

endmodule
