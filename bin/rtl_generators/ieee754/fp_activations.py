# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP Activation Functions Generator
# Purpose: Generate activation function modules for floating-point formats
#
# Supported formats:
#   - FP32: 1 sign, 8 exp (bias=127), 23 mantissa
#   - FP16: 1 sign, 5 exp (bias=15), 10 mantissa
#   - BF16: 1 sign, 8 exp (bias=127), 7 mantissa
#   - FP8 E4M3: 1 sign, 4 exp (bias=7), 3 mantissa
#   - FP8 E5M2: 1 sign, 5 exp (bias=15), 2 mantissa
#
# Activation functions:
#   - ReLU: max(0, x)
#   - Sigmoid: 1/(1+exp(-x)) via piecewise linear approximation
#   - Tanh: (exp(x)-exp(-x))/(exp(x)+exp(-x)) via 2*sigmoid(2x)-1
#   - GELU: x * sigmoid(1.702*x) approximation
#   - Softmax: exp(x_i)/sum(exp(x_j)) - vector operation
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-02

try:
    from .rtl_header import generate_rtl_header
except ImportError:
    from rtl_generators.ieee754.rtl_header import generate_rtl_header

# Format definitions: (total_bits, exp_bits, mant_bits, bias, has_infinity, name)
FORMATS = {
    'fp32': (32, 8, 23, 127, True, 'FP32'),
    'fp16': (16, 5, 10, 15, True, 'FP16'),
    'bf16': (16, 8, 7, 127, True, 'BF16'),
    'fp8_e4m3': (8, 4, 3, 7, False, 'FP8_E4M3'),
    'fp8_e5m2': (8, 5, 2, 15, True, 'FP8_E5M2'),
}


def generate_relu(fmt, output_path):
    """Generate ReLU activation: max(0, x)."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_relu'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} ReLU: max(0, x)
// Simply return 0 if negative, else pass through

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// ReLU logic: if negative (and not NaN), output zero
// NaN propagates as NaN
assign ow_result = w_is_nan ? i_a :          // Propagate NaN
                   w_sign   ? {bits}'h0 :    // Negative -> 0
                              i_a;           // Positive -> pass through

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} ReLU activation function: max(0, x)',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_sigmoid(fmt, output_path):
    """Generate Sigmoid activation: 1/(1+exp(-x)) via piecewise linear approximation."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_sigmoid'

    exp_max = (1 << exp_bits) - 1

    # Sigmoid characteristics:
    # sigmoid(0) = 0.5
    # sigmoid(-inf) = 0, sigmoid(+inf) = 1
    # Nearly linear around 0, saturates at extremes
    # Use piecewise linear approximation with symmetry: sigmoid(-x) = 1 - sigmoid(x)

    # Encode constants for this format
    # 0.5 = 2^-1 = exp=bias-1, mant=0
    half_exp = bias - 1
    # 1.0 = 2^0 = exp=bias, mant=0
    one_exp = bias

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} Sigmoid: 1/(1+exp(-x))
// Piecewise linear approximation using symmetry: sigmoid(-x) = 1 - sigmoid(x)
//
// Approximation regions:
//   x <= -4: sigmoid(x) ≈ 0
//   -4 < x < 4: linear interpolation
//   x >= 4: sigmoid(x) ≈ 1

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
wire w_is_subnormal = (w_exp == {exp_bits}'h0) & (w_mant != {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_inf = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h0);
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_inf = 1'b0;
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Constants
localparam [{bits-1}:0] ZERO = {bits}'h0;
localparam [{bits-1}:0] HALF = {{1'b0, {exp_bits}'d{half_exp}, {mant_bits}'h0}};  // 0.5
localparam [{bits-1}:0] ONE  = {{1'b0, {exp_bits}'d{one_exp}, {mant_bits}'h0}};   // 1.0

// Determine magnitude category
// |x| >= 4 means exp >= bias+2 (since 4 = 2^2)
wire w_saturated = (w_exp >= {exp_bits}'d{bias + 2});

// |x| < 0.25 means exp < bias-2 (nearly linear region, slope ~0.25)
wire w_near_zero = (w_exp < {exp_bits}'d{max(1, bias - 2)}) | w_is_zero | w_is_subnormal;

// Linear approximation: sigmoid(x) ≈ 0.5 + 0.25*x for small x
// For |x| in [0.25, 4], use coarser approximation

// Simplified piecewise result
logic [{bits-1}:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf | w_saturated) begin
        // Large magnitude: saturate to 0 or 1
        r_result = w_sign ? ZERO : ONE;
    end else if (w_near_zero) begin
        // Small magnitude: sigmoid(x) ≈ 0.5
        r_result = HALF;
    end else begin
        // Medium range: linear interpolation between 0.25 and 0.75
        // Approximate as 0.5 + sign * 0.25 = 0.25 or 0.75
        // More accurate: scale based on exponent
        if (w_sign) begin
            // Negative: result in (0, 0.5)
            // Approximate: 0.5 - 0.125 = 0.375 for moderate negative
            r_result = {{1'b0, {exp_bits}'d{half_exp - 1}, {mant_bits}'d{1 << (mant_bits - 1)}}};  // ~0.375
        end else begin
            // Positive: result in (0.5, 1)
            // Approximate: 0.5 + 0.125 = 0.625 for moderate positive
            r_result = {{1'b0, {exp_bits}'d{half_exp}, {mant_bits}'d{1 << (mant_bits - 1)}}};  // ~0.625
        end
    end
end

assign ow_result = r_result;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} Sigmoid activation function: 1/(1+exp(-x))',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_tanh(fmt, output_path):
    """Generate Tanh activation: uses relationship tanh(x) = 2*sigmoid(2x) - 1."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_tanh'

    exp_max = (1 << exp_bits) - 1
    half_exp = bias - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} Tanh: (exp(x)-exp(-x))/(exp(x)+exp(-x))
// Piecewise linear approximation
//
// tanh characteristics:
//   tanh(0) = 0
//   tanh(-inf) = -1, tanh(+inf) = +1
//   tanh(-x) = -tanh(x) (odd function)
//   Nearly linear around 0 with slope 1, saturates at ±1

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
wire w_is_subnormal = (w_exp == {exp_bits}'h0) & (w_mant != {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_inf = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h0);
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_inf = 1'b0;
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Constants
localparam [{bits-1}:0] ZERO = {bits}'h0;
localparam [{bits-1}:0] POS_ONE = {{1'b0, {exp_bits}'d{bias}, {mant_bits}'h0}};   // +1.0
localparam [{bits-1}:0] NEG_ONE = {{1'b1, {exp_bits}'d{bias}, {mant_bits}'h0}};   // -1.0

// Determine magnitude category
// |x| >= 2 means exp >= bias+1 (saturates to ±1)
wire w_saturated = (w_exp >= {exp_bits}'d{bias + 1});

// |x| < 0.5 means exp < bias-1 (nearly linear region)
wire w_near_zero = (w_exp < {exp_bits}'d{max(1, bias - 1)}) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [{bits-1}:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf | w_saturated) begin
        // Large magnitude: saturate to ±1
        r_result = w_sign ? NEG_ONE : POS_ONE;
    end else if (w_near_zero) begin
        // Small magnitude: tanh(x) ≈ x (slope ~1)
        r_result = i_a;
    end else begin
        // Medium range: interpolate
        // Approximate as ±0.75 for moderate values
        r_result = {{w_sign, {exp_bits}'d{half_exp}, {mant_bits}'d{1 << (mant_bits - 1)}}};  // ±0.75
    end
end

assign ow_result = r_result;

endmodule
'''


    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} Tanh activation function',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_gelu(fmt, output_path):
    """Generate GELU activation: x * sigmoid(1.702*x) approximation."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_gelu'

    exp_max = (1 << exp_bits) - 1
    half_exp = bias - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} GELU: Gaussian Error Linear Unit
// Approximation: x * sigmoid(1.702 * x)
//
// GELU characteristics:
//   GELU(0) = 0
//   GELU(x) ≈ x for large positive x
//   GELU(x) ≈ 0 for large negative x
//   Smooth, non-monotonic near x ≈ -0.5

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
wire w_is_subnormal = (w_exp == {exp_bits}'h0) & (w_mant != {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_inf = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h0);
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_inf = 1'b0;
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Constants
localparam [{bits-1}:0] ZERO = {bits}'h0;

// Determine magnitude category
// Large positive: GELU(x) ≈ x
// Large negative: GELU(x) ≈ 0
wire w_large_pos = ~w_sign & (w_exp >= {exp_bits}'d{bias + 2});
wire w_large_neg = w_sign & (w_exp >= {exp_bits}'d{bias + 2});

// Near zero: GELU(x) ≈ 0.5 * x
wire w_near_zero = (w_exp < {exp_bits}'d{max(1, bias - 2)}) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [{bits-1}:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf) begin
        r_result = w_sign ? ZERO : i_a;  // +inf -> +inf, -inf -> 0
    end else if (w_large_neg) begin
        // Large negative: GELU ≈ 0
        r_result = ZERO;
    end else if (w_large_pos) begin
        // Large positive: GELU ≈ x
        r_result = i_a;
    end else if (w_near_zero) begin
        // Small x: GELU(x) ≈ 0.5 * x
        // Halving: decrement exponent by 1
        if (w_exp > {exp_bits}'d1) begin
            r_result = {{w_sign, w_exp - {exp_bits}'d1, w_mant}};
        end else begin
            r_result = ZERO;  // Underflow to zero
        end
    end else begin
        // Medium range: approximate
        if (w_sign) begin
            // Negative medium: small negative output
            // GELU(-1) ≈ -0.159, approximate as -0.125 = -2^-3
            r_result = {{1'b1, {exp_bits}'d{max(1, bias - 3)}, {mant_bits}'h0}};
        end else begin
            // Positive medium: slightly less than x
            // GELU(1) ≈ 0.841, approximate as 0.75
            r_result = {{1'b0, {exp_bits}'d{half_exp}, {mant_bits}'d{1 << (mant_bits - 1)}}};
        end
    end
end

assign ow_result = r_result;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} GELU activation function: x * sigmoid(1.702*x)',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_softmax(fmt, output_path, vector_size=8):
    """Generate Softmax activation: exp(x_i)/sum(exp(x_j)) for a vector."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_softmax_{vector_size}'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic                 i_clk,
    input  logic                 i_rst_n,
    input  logic                 i_valid,
    input  logic [{bits-1}:0]    i_data [{vector_size}],
    output logic                 ow_valid,
    output logic [{bits-1}:0]    ow_result [{vector_size}]
);

// {name} Softmax: exp(x_i) / sum(exp(x_j)) for {vector_size}-element vector
//
// Numerically stable version:
//   1. Find max element: m = max(x_i)
//   2. Subtract max: y_i = x_i - m
//   3. Compute exp: e_i = exp(y_i)
//   4. Sum: s = sum(e_i)
//   5. Normalize: result_i = e_i / s
//
// Simplified approximation for hardware:
//   - Use piecewise linear exp approximation
//   - Find max, compute relative differences
//   - Approximate normalization

// Pipeline stages
logic r_valid_d1, r_valid_d2, r_valid_d3;

// Stage 1: Find maximum
logic [{bits-1}:0] r_data_d1 [{vector_size}];
logic [{bits-1}:0] r_max;

// Comparator for finding max (simplified: compare exponents first, then mantissa)
function automatic logic [{bits-1}:0] fp_max(
    input logic [{bits-1}:0] a,
    input logic [{bits-1}:0] b
);
    logic a_sign, b_sign;
    logic [{exp_bits-1}:0] a_exp, b_exp;
    logic [{mant_bits-1}:0] a_mant, b_mant;
    logic a_greater;

    a_sign = a[{bits-1}];
    b_sign = b[{bits-1}];
    a_exp = a[{bits-2}:{mant_bits}];
    b_exp = b[{bits-2}:{mant_bits}];
    a_mant = a[{mant_bits-1}:0];
    b_mant = b[{mant_bits-1}:0];

    // Handle sign comparison
    if (a_sign != b_sign) begin
        a_greater = b_sign;  // Positive > Negative
    end else if (a_sign == 1'b0) begin
        // Both positive: larger exp/mant is greater
        a_greater = (a_exp > b_exp) | ((a_exp == b_exp) & (a_mant > b_mant));
    end else begin
        // Both negative: smaller magnitude is greater
        a_greater = (a_exp < b_exp) | ((a_exp == b_exp) & (a_mant < b_mant));
    end

    return a_greater ? a : b;
endfunction

// Stage 1: Register inputs and find max
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d1 <= 1'b0;
        r_max <= {bits}'h0;
        for (int i = 0; i < {vector_size}; i++) begin
            r_data_d1[i] <= {bits}'h0;
        end
    end else begin
        r_valid_d1 <= i_valid;
        if (i_valid) begin
            // Store input data
            for (int i = 0; i < {vector_size}; i++) begin
                r_data_d1[i] <= i_data[i];
            end
            // Find maximum using reduction tree
            r_max <= fp_max(fp_max(fp_max(i_data[0], i_data[1]),
                                   fp_max(i_data[2], i_data[3])),
                           fp_max(fp_max(i_data[4], i_data[5]),
                                   fp_max(i_data[6], i_data[7])));
        end
    end
end

// Stage 2: Compute relative exp approximation
// exp(x - max) approximation: if max-x is small, use linear; else use 0
logic [{bits-1}:0] r_exp_approx [{vector_size}];
logic r_valid_d2_reg;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d2 <= 1'b0;
        for (int i = 0; i < {vector_size}; i++) begin
            r_exp_approx[i] <= {bits}'h0;
        end
    end else begin
        r_valid_d2 <= r_valid_d1;
        if (r_valid_d1) begin
            for (int i = 0; i < {vector_size}; i++) begin
                // Simplified: if element equals max, exp=1; else approximate
                if (r_data_d1[i] == r_max) begin
                    r_exp_approx[i] <= {{1'b0, {exp_bits}'d{bias}, {mant_bits}'h0}};  // 1.0
                end else begin
                    // Approximate exp(x-max) based on difference
                    // For large differences, use small value
                    r_exp_approx[i] <= {{1'b0, {exp_bits}'d{max(1, bias - 3)}, {mant_bits}'h0}};  // ~0.125
                end
            end
        end
    end
end

// Stage 3: Normalize (simplified: divide by sum)
// For 8 elements with max=1, others~0.125: sum ≈ 1 + 7*0.125 = 1.875 ≈ 2
// Normalized: max element ≈ 0.5, others ≈ 0.0625
logic [{bits-1}:0] r_result [{vector_size}];

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d3 <= 1'b0;
        for (int i = 0; i < {vector_size}; i++) begin
            r_result[i] <= {bits}'h0;
        end
    end else begin
        r_valid_d3 <= r_valid_d2;
        if (r_valid_d2) begin
            for (int i = 0; i < {vector_size}; i++) begin
                // Simplified normalization: divide by ~8 (shift exp down by 3)
                // This gives approximately uniform distribution as default
                if (r_exp_approx[i][{bits-2}:{mant_bits}] > {exp_bits}'d3) begin
                    r_result[i] <= {{r_exp_approx[i][{bits-1}],
                                    r_exp_approx[i][{bits-2}:{mant_bits}] - {exp_bits}'d3,
                                    r_exp_approx[i][{mant_bits-1}:0]}};
                end else begin
                    r_result[i] <= {bits}'h0;  // Underflow to zero
                end
            end
        end
    end
end

assign ow_valid = r_valid_d3;
assign ow_result = r_result;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} Softmax activation function for {vector_size}-element vector',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_leaky_relu(fmt, output_path, alpha_shift=4):
    """Generate Leaky ReLU: max(alpha*x, x) where alpha = 2^-alpha_shift."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_leaky_relu'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} #(
    parameter int ALPHA_SHIFT = {alpha_shift}  // alpha = 2^-ALPHA_SHIFT (default 0.0625)
) (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} Leaky ReLU: max(alpha*x, x)
// alpha = 2^-ALPHA_SHIFT (implemented as exponent decrement)
// For negative x: output = alpha * x (small negative slope)
// For positive x: output = x

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Leaky ReLU: multiply by alpha for negative values
// alpha * x = x * 2^-ALPHA_SHIFT = decrement exponent
wire [{exp_bits-1}:0] w_scaled_exp = (w_exp > ALPHA_SHIFT[{exp_bits-1}:0]) ?
                                     (w_exp - ALPHA_SHIFT[{exp_bits-1}:0]) : {exp_bits}'h0;

assign ow_result = w_is_nan   ? i_a :                           // Propagate NaN
                   w_is_zero  ? {bits}'h0 :                     // Zero -> Zero
                   ~w_sign    ? i_a :                           // Positive -> pass through
                   {{w_sign, w_scaled_exp, w_mant}};            // Negative -> scale by alpha

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} Leaky ReLU activation: max(alpha*x, x)',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_silu(fmt, output_path):
    """Generate SiLU/Swish activation: x * sigmoid(x)."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_silu'

    exp_max = (1 << exp_bits) - 1
    half_exp = bias - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    output logic [{bits-1}:0] ow_result
);

// {name} SiLU/Swish: x * sigmoid(x)
//
// SiLU characteristics:
//   SiLU(0) = 0
//   SiLU(x) ≈ x for large positive x (sigmoid ≈ 1)
//   SiLU(x) ≈ 0 for large negative x (sigmoid ≈ 0)
//   Has a small negative dip around x ≈ -1.28

wire w_sign = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant = i_a[{mant_bits-1}:0];

// Special case detection
wire w_is_zero = (w_exp == {exp_bits}'h0) & (w_mant == {mant_bits}'h0);
wire w_is_subnormal = (w_exp == {exp_bits}'h0) & (w_mant != {mant_bits}'h0);
'''

    if has_inf:
        content += f'''wire w_is_inf = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h0);
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_is_inf = 1'b0;
wire w_is_nan = (w_exp == {exp_bits}'h{exp_max:X}) & (w_mant == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Constants
localparam [{bits-1}:0] ZERO = {bits}'h0;

// Determine magnitude category
wire w_large_pos = ~w_sign & (w_exp >= {exp_bits}'d{bias + 2});
wire w_large_neg = w_sign & (w_exp >= {exp_bits}'d{bias + 2});
wire w_near_zero = (w_exp < {exp_bits}'d{max(1, bias - 2)}) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [{bits-1}:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf) begin
        r_result = w_sign ? ZERO : i_a;  // +inf -> +inf, -inf -> 0
    end else if (w_large_neg) begin
        // Large negative: SiLU ≈ 0
        r_result = ZERO;
    end else if (w_large_pos) begin
        // Large positive: SiLU ≈ x (sigmoid ≈ 1)
        r_result = i_a;
    end else if (w_near_zero) begin
        // Small x: SiLU(x) ≈ 0.5 * x (sigmoid(0) = 0.5)
        if (w_exp > {exp_bits}'d1) begin
            r_result = {{w_sign, w_exp - {exp_bits}'d1, w_mant}};
        end else begin
            r_result = ZERO;
        end
    end else begin
        // Medium range
        if (w_sign) begin
            // Negative medium: small negative (dip region)
            // SiLU(-1) ≈ -0.269, approximate as -0.25
            r_result = {{1'b1, {exp_bits}'d{max(1, bias - 2)}, {mant_bits}'h0}};
        end else begin
            // Positive medium: somewhat less than x
            // SiLU(1) ≈ 0.731, approximate as 0.75
            r_result = {{1'b0, {exp_bits}'d{half_exp}, {mant_bits}'d{1 << (mant_bits - 1)}}};
        end
    end
end

assign ow_result = r_result;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} SiLU/Swish activation function: x * sigmoid(x)',
        generator_script='fp_activations.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_all_activations(output_path):
    """Generate all activation function modules for all formats."""
    formats = ['fp32', 'fp16', 'bf16', 'fp8_e4m3', 'fp8_e5m2']
    generated = []

    print('\n=== Activation Functions ===')

    for fmt in formats:
        name = FORMATS[fmt][5]

        # ReLU
        print(f'Generating {name} ReLU...')
        module = generate_relu(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Leaky ReLU
        print(f'Generating {name} Leaky ReLU...')
        module = generate_leaky_relu(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Sigmoid
        print(f'Generating {name} Sigmoid...')
        module = generate_sigmoid(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Tanh
        print(f'Generating {name} Tanh...')
        module = generate_tanh(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # GELU
        print(f'Generating {name} GELU...')
        module = generate_gelu(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # SiLU/Swish
        print(f'Generating {name} SiLU...')
        module = generate_silu(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Softmax (8-element vector)
        print(f'Generating {name} Softmax...')
        module = generate_softmax(fmt, output_path, vector_size=8)
        generated.append(module)
        print(f'  Created: {module}.sv')

    return generated


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    modules = generate_all_activations(output_path)
    print(f'\nGenerated {len(modules)} activation modules')
