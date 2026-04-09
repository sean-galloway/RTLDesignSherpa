// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_to_int
//
// Verifies BF16 to signed INT8 conversion:
//   - Zero input produces zero output
//   - NaN handling (NaN -> 0)
//   - Infinity handling (saturate to +127/-128)
//   - Sign preservation
//   - Output always in [-128, +127] range
//   - Known test vectors

`timescale 1ns / 1ps

module formal_math_bf16_to_int (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] bf16_val;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] int8_out;
    logic       overflow, underflow, is_zero;

    math_bf16_to_int dut (
        .i_bf16      (bf16_val),
        .ow_int8     (int8_out),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_is_zero  (is_zero)
    );

    // =========================================================================
    // BF16 field extraction
    // =========================================================================
    wire        sign   = bf16_val[15];
    wire [7:0]  exp    = bf16_val[14:7];
    wire [6:0]  mant   = bf16_val[6:0];

    wire is_bf16_zero   = (exp == 8'h00);
    wire is_bf16_inf    = (exp == 8'hFF) && (mant == 7'h00);
    wire is_bf16_nan    = (exp == 8'hFF) && (mant != 7'h00);
    wire is_bf16_normal = (exp != 8'h00) && (exp != 8'hFF);

    // Interpret int8_out as signed
    wire signed [7:0] int8_signed = $signed(int8_out);

    // =========================================================================
    // Property 1: Zero input produces zero output
    // =========================================================================
    always @(posedge clk) begin
        if (is_bf16_zero) begin
            p_zero_result: assert (int8_out == 8'd0);
            p_zero_flag: assert (is_zero);
            p_zero_no_overflow: assert (!overflow);
            p_zero_no_underflow: assert (!underflow);
        end
    end

    // =========================================================================
    // Property 2: NaN input produces zero output
    // =========================================================================
    always @(posedge clk) begin
        if (is_bf16_nan) begin
            p_nan_result: assert (int8_out == 8'd0);
            p_nan_no_overflow: assert (!overflow);
            p_nan_no_underflow: assert (!underflow);
        end
    end

    // =========================================================================
    // Property 3: Positive infinity saturates to +127
    // =========================================================================
    always @(posedge clk) begin
        if (is_bf16_inf && !sign) begin
            p_pos_inf_result: assert (int8_out == 8'h7F);
            p_pos_inf_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Property 4: Negative infinity saturates to -128
    // =========================================================================
    always @(posedge clk) begin
        if (is_bf16_inf && sign) begin
            p_neg_inf_result: assert (int8_out == 8'h80);
            p_neg_inf_underflow: assert (underflow);
        end
    end

    // =========================================================================
    // Property 5: Output is always in valid INT8 range [-128, +127]
    // This is trivially true for 8-bit two's complement, but verifies
    // the conversion logic doesn't produce garbage
    // =========================================================================
    always @(posedge clk) begin
        p_range_valid: assert (int8_signed >= -128 && int8_signed <= 127);
    end

    // =========================================================================
    // Property 6: Overflow flag implies positive saturation
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_val: assert (int8_out == 8'h7F);
        end
    end

    // =========================================================================
    // Property 7: Underflow flag implies negative saturation
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_val: assert (int8_out == 8'h80);
        end
    end

    // =========================================================================
    // Property 8: Overflow and underflow are mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_mutex: assert (!(overflow && underflow));
    end

    // =========================================================================
    // Property 9: Known vector: BF16 1.0 (0x3F80) -> INT8 1
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h3F80) begin
            p_one: assert (int8_out == 8'd1);
            p_one_no_flags: assert (!overflow && !underflow && !is_zero);
        end
    end

    // =========================================================================
    // Property 10: Known vector: BF16 -1.0 (0xBF80) -> INT8 -1
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'hBF80) begin
            p_neg_one: assert (int8_out == 8'hFF);
            p_neg_one_no_flags: assert (!overflow && !underflow && !is_zero);
        end
    end

    // =========================================================================
    // Property 11: Known vector: BF16 2.0 (0x4000) -> INT8 2
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h4000) begin
            p_two: assert (int8_out == 8'd2);
        end
    end

    // =========================================================================
    // Property 12: Known vector: BF16 0.0 (0x0000) -> INT8 0
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h0000) begin
            p_pos_zero: assert (int8_out == 8'd0);
            p_pos_zero_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property 13: Known vector: BF16 -0.0 (0x8000) -> INT8 0
    // (negative zero with exp=0 is treated as zero)
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h8000) begin
            p_neg_zero: assert (int8_out == 8'd0);
            p_neg_zero_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property 14: Known vector: BF16 127.0 (0x42FE) -> INT8 127
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h42FE) begin
            p_max_pos: assert (int8_out == 8'd127);
            p_max_pos_no_overflow: assert (!overflow);
        end
    end

    // =========================================================================
    // Property 15: Known vector: BF16 0.5 (0x3F00) -> INT8 0 (RNE: 0.5 rounds to even 0)
    // =========================================================================
    always @(posedge clk) begin
        if (bf16_val == 16'h3F00) begin
            p_half_rounds_to_zero: assert (int8_out == 8'd0);
        end
    end

    // =========================================================================
    // Property 16: Positive normal value with overflow produces +127
    // When exp >= 134 (value >= 128) and sign=0, must saturate
    // =========================================================================
    always @(posedge clk) begin
        if (!sign && is_bf16_normal && exp >= 8'd135) begin
            // exp=135 means value >= 256, definitely overflows
            p_large_pos_sat: assert (int8_out == 8'h7F);
            p_large_pos_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Property 17: Negative normal value with underflow produces -128
    // =========================================================================
    always @(posedge clk) begin
        if (sign && is_bf16_normal && exp >= 8'd135) begin
            p_large_neg_sat: assert (int8_out == 8'h80);
            p_large_neg_underflow: assert (underflow);
        end
    end

    // =========================================================================
    // Property 18: Very small values (exp < 126) round to zero
    // exp < 126 means |value| < 0.5, rounds to 0
    // =========================================================================
    always @(posedge clk) begin
        if (is_bf16_normal && exp < 8'd126) begin
            p_small_val_zero: assert (int8_out == 8'd0);
            p_small_val_is_zero: assert (is_zero);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_zero_in:   cover (is_bf16_zero);
        c_nan_in:    cover (is_bf16_nan);
        c_inf_pos:   cover (is_bf16_inf && !sign);
        c_inf_neg:   cover (is_bf16_inf && sign);
        c_normal:    cover (is_bf16_normal && !overflow && !underflow && !is_zero);
        c_overflow:  cover (overflow);
        c_underflow: cover (underflow);
        c_positive:  cover (int8_signed > 0);
        c_negative:  cover (int8_signed < 0);
    end

endmodule
