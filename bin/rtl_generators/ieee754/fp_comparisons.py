# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP Comparison Operations Generator
# Purpose: Generate comparison modules for floating-point formats
#
# Supported formats:
#   - FP32: 1 sign, 8 exp (bias=127), 23 mantissa
#   - FP16: 1 sign, 5 exp (bias=15), 10 mantissa
#   - BF16: 1 sign, 8 exp (bias=127), 7 mantissa
#   - FP8 E4M3: 1 sign, 4 exp (bias=7), 3 mantissa
#   - FP8 E5M2: 1 sign, 5 exp (bias=15), 2 mantissa
#
# Comparison operations:
#   - Comparator: Full comparison with EQ, LT, GT, LE, GE, NE flags
#   - Max: Returns maximum of two values
#   - Min: Returns minimum of two values
#   - Max Tree: Finds maximum across N values (reduction tree)
#   - Min Tree: Finds minimum across N values (reduction tree)
#   - Clamp: Clamps value to [min, max] range
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


def generate_comparator(fmt, output_path):
    """Generate full comparator with all comparison flags."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_comparator'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    input  logic [{bits-1}:0] i_b,
    output logic              ow_eq,    // a == b
    output logic              ow_lt,    // a < b
    output logic              ow_gt,    // a > b
    output logic              ow_le,    // a <= b
    output logic              ow_ge,    // a >= b
    output logic              ow_ne,    // a != b
    output logic              ow_unord  // Unordered (either is NaN)
);

// {name} Comparator
// IEEE 754 comparison semantics:
// - NaN compares unordered with everything (including itself)
// - +0 == -0
// - Infinity compares as expected

// Field extraction - A
wire w_sign_a = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp_a = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_a = i_a[{mant_bits-1}:0];

// Field extraction - B
wire w_sign_b = i_b[{bits-1}];
wire [{exp_bits-1}:0] w_exp_b = i_b[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_b = i_b[{mant_bits-1}:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == {exp_bits}'h0) & (w_mant_a == {mant_bits}'h0);
wire w_b_is_zero = (w_exp_b == {exp_bits}'h0) & (w_mant_b == {mant_bits}'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;
'''

    if has_inf:
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a != {mant_bits}'h0);
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b != {mant_bits}'h0);
'''
    else:
        # E4M3: NaN is exp=15, mant=7
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a == {mant_bits}'h{(1 << mant_bits) - 1:X});
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
wire w_either_nan = w_a_is_nan | w_b_is_nan;

// Magnitude comparison (treating as unsigned integers, ignoring sign)
// For positive numbers: larger exp/mant means larger value
// For negative numbers: larger exp/mant means smaller value (more negative)
wire [{bits-2}:0] w_mag_a = i_a[{bits-2}:0];  // exp + mant
wire [{bits-2}:0] w_mag_b = i_b[{bits-2}:0];

wire w_mag_a_gt_b = w_mag_a > w_mag_b;
wire w_mag_a_lt_b = w_mag_a < w_mag_b;
wire w_mag_eq = (w_mag_a == w_mag_b);

// Determine ordering
logic w_a_less_than_b;
logic w_a_equal_b;

always_comb begin
    // Default: compare magnitudes
    w_a_equal_b = 1'b0;
    w_a_less_than_b = 1'b0;

    if (w_both_zero) begin
        // +0 == -0
        w_a_equal_b = 1'b1;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: negative is less
        w_a_less_than_b = w_sign_a;  // a is negative, so a < b
    end else if (w_sign_a == 1'b0) begin
        // Both positive: larger magnitude is greater
        w_a_less_than_b = w_mag_a_lt_b;
        w_a_equal_b = w_mag_eq;
    end else begin
        // Both negative: larger magnitude is less (more negative)
        w_a_less_than_b = w_mag_a_gt_b;
        w_a_equal_b = w_mag_eq;
    end
end

// Output assignments
assign ow_unord = w_either_nan;
assign ow_eq = ~w_either_nan & w_a_equal_b;
assign ow_lt = ~w_either_nan & w_a_less_than_b;
assign ow_gt = ~w_either_nan & ~w_a_less_than_b & ~w_a_equal_b;
assign ow_le = ~w_either_nan & (w_a_less_than_b | w_a_equal_b);
assign ow_ge = ~w_either_nan & (~w_a_less_than_b | w_a_equal_b);
assign ow_ne = ~w_either_nan & ~w_a_equal_b;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} comparator with EQ/LT/GT/LE/GE/NE/UNORD flags',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_max(fmt, output_path):
    """Generate max(a, b) module."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_max'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    input  logic [{bits-1}:0] i_b,
    output logic [{bits-1}:0] ow_result
);

// {name} Max: returns maximum of two values
// IEEE 754 semantics:
// - If either is NaN, return the non-NaN (or NaN if both)
// - max(+0, -0) = +0

// Field extraction - A
wire w_sign_a = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp_a = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_a = i_a[{mant_bits-1}:0];

// Field extraction - B
wire w_sign_b = i_b[{bits-1}];
wire [{exp_bits-1}:0] w_exp_b = i_b[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_b = i_b[{mant_bits-1}:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == {exp_bits}'h0) & (w_mant_a == {mant_bits}'h0);
wire w_b_is_zero = (w_exp_b == {exp_bits}'h0) & (w_mant_b == {mant_bits}'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;
'''

    if has_inf:
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a != {mant_bits}'h0);
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b != {mant_bits}'h0);
'''
    else:
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a == {mant_bits}'h{(1 << mant_bits) - 1:X});
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Magnitude comparison
wire [{bits-2}:0] w_mag_a = i_a[{bits-2}:0];
wire [{bits-2}:0] w_mag_b = i_b[{bits-2}:0];

// Determine which is greater
logic w_a_greater;

always_comb begin
    if (w_both_zero) begin
        // max(+0, -0) = +0: prefer non-negative
        w_a_greater = ~w_sign_a;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: positive is greater
        w_a_greater = ~w_sign_a;
    end else if (w_sign_a == 1'b0) begin
        // Both positive: larger magnitude is greater
        w_a_greater = (w_mag_a >= w_mag_b);
    end else begin
        // Both negative: smaller magnitude is greater (less negative)
        w_a_greater = (w_mag_a <= w_mag_b);
    end
end

// Result selection
assign ow_result = w_a_is_nan ? i_b :      // a is NaN, return b
                   w_b_is_nan ? i_a :      // b is NaN, return a
                   w_a_greater ? i_a : i_b;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} maximum of two values',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_min(fmt, output_path):
    """Generate min(a, b) module."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_min'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_a,
    input  logic [{bits-1}:0] i_b,
    output logic [{bits-1}:0] ow_result
);

// {name} Min: returns minimum of two values
// IEEE 754 semantics:
// - If either is NaN, return the non-NaN (or NaN if both)
// - min(+0, -0) = -0

// Field extraction - A
wire w_sign_a = i_a[{bits-1}];
wire [{exp_bits-1}:0] w_exp_a = i_a[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_a = i_a[{mant_bits-1}:0];

// Field extraction - B
wire w_sign_b = i_b[{bits-1}];
wire [{exp_bits-1}:0] w_exp_b = i_b[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_b = i_b[{mant_bits-1}:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == {exp_bits}'h0) & (w_mant_a == {mant_bits}'h0);
wire w_b_is_zero = (w_exp_b == {exp_bits}'h0) & (w_mant_b == {mant_bits}'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;
'''

    if has_inf:
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a != {mant_bits}'h0);
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b != {mant_bits}'h0);
'''
    else:
        content += f'''
wire w_a_is_nan = (w_exp_a == {exp_bits}'h{exp_max:X}) & (w_mant_a == {mant_bits}'h{(1 << mant_bits) - 1:X});
wire w_b_is_nan = (w_exp_b == {exp_bits}'h{exp_max:X}) & (w_mant_b == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''
// Magnitude comparison
wire [{bits-2}:0] w_mag_a = i_a[{bits-2}:0];
wire [{bits-2}:0] w_mag_b = i_b[{bits-2}:0];

// Determine which is less
logic w_a_less;

always_comb begin
    if (w_both_zero) begin
        // min(+0, -0) = -0: prefer negative
        w_a_less = w_sign_a;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: negative is less
        w_a_less = w_sign_a;
    end else if (w_sign_a == 1'b0) begin
        // Both positive: smaller magnitude is less
        w_a_less = (w_mag_a <= w_mag_b);
    end else begin
        // Both negative: larger magnitude is less (more negative)
        w_a_less = (w_mag_a >= w_mag_b);
    end
end

// Result selection
assign ow_result = w_a_is_nan ? i_b :    // a is NaN, return b
                   w_b_is_nan ? i_a :    // b is NaN, return a
                   w_a_less ? i_a : i_b;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} minimum of two values',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_max_tree(fmt, output_path, size=8):
    """Generate max reduction tree for N values."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_max_tree_{size}'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_data [{size}],
    output logic [{bits-1}:0] ow_max,
    output logic [{size-1}:0] ow_max_idx  // One-hot index of maximum
);

// {name} Max Tree: finds maximum of {size} values
// Uses binary reduction tree for O(log N) depth

'''

    # Generate comparison function
    if has_inf:
        nan_check_a = f"(a[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (a[{mant_bits-1}:0] != {mant_bits}'h0)"
        nan_check_b = f"(b[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (b[{mant_bits-1}:0] != {mant_bits}'h0)"
    else:
        nan_check_a = f"(a[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (a[{mant_bits-1}:0] == {mant_bits}'h{(1 << mant_bits) - 1:X})"
        nan_check_b = f"(b[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (b[{mant_bits-1}:0] == {mant_bits}'h{(1 << mant_bits) - 1:X})"

    content += f'''// Max function for two values
function automatic logic [{bits-1}:0] fp_max(
    input logic [{bits-1}:0] a,
    input logic [{bits-1}:0] b
);
    logic a_sign, b_sign;
    logic [{bits-2}:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;
    logic a_greater;

    a_sign = a[{bits-1}];
    b_sign = b[{bits-1}];
    a_mag = a[{bits-2}:0];
    b_mag = b[{bits-2}:0];
    a_is_nan = {nan_check_a};
    b_is_nan = {nan_check_b};

    // Handle NaN
    if (a_is_nan) return b;
    if (b_is_nan) return a;

    // Compare
    if (a_sign != b_sign) begin
        a_greater = ~a_sign;  // Positive > negative
    end else if (a_sign == 1'b0) begin
        a_greater = (a_mag >= b_mag);
    end else begin
        a_greater = (a_mag <= b_mag);
    end

    return a_greater ? a : b;
endfunction

// Comparison function returning 1 if a > b
function automatic logic fp_gt(
    input logic [{bits-1}:0] a,
    input logic [{bits-1}:0] b
);
    logic a_sign, b_sign;
    logic [{bits-2}:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;

    a_sign = a[{bits-1}];
    b_sign = b[{bits-1}];
    a_mag = a[{bits-2}:0];
    b_mag = b[{bits-2}:0];
    a_is_nan = {nan_check_a};
    b_is_nan = {nan_check_b};

    if (a_is_nan | b_is_nan) return 1'b0;

    if (a_sign != b_sign) begin
        return ~a_sign;
    end else if (a_sign == 1'b0) begin
        return (a_mag > b_mag);
    end else begin
        return (a_mag < b_mag);
    end
endfunction

// Binary reduction tree
'''

    # Generate tree levels
    # Level 0: 8 inputs -> 4 outputs
    # Level 1: 4 inputs -> 2 outputs
    # Level 2: 2 inputs -> 1 output
    import math
    levels = int(math.log2(size))

    for level in range(levels):
        inputs = size >> level
        outputs = inputs >> 1
        content += f'''
// Level {level}: {inputs} -> {outputs}
logic [{bits-1}:0] w_level{level} [{outputs}];
'''
        for i in range(outputs):
            if level == 0:
                content += f'''assign w_level{level}[{i}] = fp_max(i_data[{2*i}], i_data[{2*i+1}]);
'''
            else:
                content += f'''assign w_level{level}[{i}] = fp_max(w_level{level-1}[{2*i}], w_level{level-1}[{2*i+1}]);
'''

    content += f'''
// Final output
assign ow_max = w_level{levels-1}[0];

// Generate one-hot index of maximum
// Compare each input against the maximum
genvar gi;
generate
    for (gi = 0; gi < {size}; gi = gi + 1) begin : gen_idx
        assign ow_max_idx[gi] = (i_data[gi] == ow_max);
    end
endgenerate

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} maximum tree reduction for {size} values',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_min_tree(fmt, output_path, size=8):
    """Generate min reduction tree for N values."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_min_tree_{size}'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_data [{size}],
    output logic [{bits-1}:0] ow_min,
    output logic [{size-1}:0] ow_min_idx  // One-hot index of minimum
);

// {name} Min Tree: finds minimum of {size} values
// Uses binary reduction tree for O(log N) depth

'''

    # Generate comparison function
    if has_inf:
        nan_check_a = f"(a[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (a[{mant_bits-1}:0] != {mant_bits}'h0)"
        nan_check_b = f"(b[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (b[{mant_bits-1}:0] != {mant_bits}'h0)"
    else:
        nan_check_a = f"(a[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (a[{mant_bits-1}:0] == {mant_bits}'h{(1 << mant_bits) - 1:X})"
        nan_check_b = f"(b[{bits-2}:{mant_bits}] == {exp_bits}'h{exp_max:X}) & (b[{mant_bits-1}:0] == {mant_bits}'h{(1 << mant_bits) - 1:X})"

    content += f'''// Min function for two values
function automatic logic [{bits-1}:0] fp_min(
    input logic [{bits-1}:0] a,
    input logic [{bits-1}:0] b
);
    logic a_sign, b_sign;
    logic [{bits-2}:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;
    logic a_less;

    a_sign = a[{bits-1}];
    b_sign = b[{bits-1}];
    a_mag = a[{bits-2}:0];
    b_mag = b[{bits-2}:0];
    a_is_nan = {nan_check_a};
    b_is_nan = {nan_check_b};

    // Handle NaN
    if (a_is_nan) return b;
    if (b_is_nan) return a;

    // Compare
    if (a_sign != b_sign) begin
        a_less = a_sign;  // Negative < positive
    end else if (a_sign == 1'b0) begin
        a_less = (a_mag <= b_mag);
    end else begin
        a_less = (a_mag >= b_mag);
    end

    return a_less ? a : b;
endfunction

// Binary reduction tree
'''

    # Generate tree levels
    import math
    levels = int(math.log2(size))

    for level in range(levels):
        inputs = size >> level
        outputs = inputs >> 1
        content += f'''
// Level {level}: {inputs} -> {outputs}
logic [{bits-1}:0] w_level{level} [{outputs}];
'''
        for i in range(outputs):
            if level == 0:
                content += f'''assign w_level{level}[{i}] = fp_min(i_data[{2*i}], i_data[{2*i+1}]);
'''
            else:
                content += f'''assign w_level{level}[{i}] = fp_min(w_level{level-1}[{2*i}], w_level{level-1}[{2*i+1}]);
'''

    content += f'''
// Final output
assign ow_min = w_level{levels-1}[0];

// Generate one-hot index of minimum
genvar gi;
generate
    for (gi = 0; gi < {size}; gi = gi + 1) begin : gen_idx
        assign ow_min_idx[gi] = (i_data[gi] == ow_min);
    end
endgenerate

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} minimum tree reduction for {size} values',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_clamp(fmt, output_path):
    """Generate clamp(x, min, max) module."""
    bits, exp_bits, mant_bits, bias, has_inf, name = FORMATS[fmt]
    module_name = f'math_{fmt}_clamp'

    exp_max = (1 << exp_bits) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{bits-1}:0] i_x,
    input  logic [{bits-1}:0] i_min,
    input  logic [{bits-1}:0] i_max,
    output logic [{bits-1}:0] ow_result
);

// {name} Clamp: clamp(x, min, max) = min(max(x, min), max)
// Returns x constrained to [min, max] range

// Field extraction
wire w_sign_x = i_x[{bits-1}];
wire [{exp_bits-1}:0] w_exp_x = i_x[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_x = i_x[{mant_bits-1}:0];

wire w_sign_min = i_min[{bits-1}];
wire [{exp_bits-1}:0] w_exp_min = i_min[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_min = i_min[{mant_bits-1}:0];

wire w_sign_max = i_max[{bits-1}];
wire [{exp_bits-1}:0] w_exp_max = i_max[{bits-2}:{mant_bits}];
wire [{mant_bits-1}:0] w_mant_max = i_max[{mant_bits-1}:0];

// NaN detection
'''

    if has_inf:
        content += f'''wire w_x_is_nan = (w_exp_x == {exp_bits}'h{exp_max:X}) & (w_mant_x != {mant_bits}'h0);
wire w_min_is_nan = (w_exp_min == {exp_bits}'h{exp_max:X}) & (w_mant_min != {mant_bits}'h0);
wire w_max_is_nan = (w_exp_max == {exp_bits}'h{exp_max:X}) & (w_mant_max != {mant_bits}'h0);
'''
    else:
        content += f'''wire w_x_is_nan = (w_exp_x == {exp_bits}'h{exp_max:X}) & (w_mant_x == {mant_bits}'h{(1 << mant_bits) - 1:X});
wire w_min_is_nan = (w_exp_min == {exp_bits}'h{exp_max:X}) & (w_mant_min == {mant_bits}'h{(1 << mant_bits) - 1:X});
wire w_max_is_nan = (w_exp_max == {exp_bits}'h{exp_max:X}) & (w_mant_max == {mant_bits}'h{(1 << mant_bits) - 1:X});
'''

    content += f'''wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

// Magnitude for comparison
wire [{bits-2}:0] w_mag_x = i_x[{bits-2}:0];
wire [{bits-2}:0] w_mag_min = i_min[{bits-2}:0];
wire [{bits-2}:0] w_mag_max = i_max[{bits-2}:0];

// Comparison logic
function automatic logic fp_less_than(
    input logic [{bits-1}:0] a,
    input logic [{bits-1}:0] b
);
    logic a_sign, b_sign;
    logic [{bits-2}:0] a_mag, b_mag;

    a_sign = a[{bits-1}];
    b_sign = b[{bits-1}];
    a_mag = a[{bits-2}:0];
    b_mag = b[{bits-2}:0];

    if (a_sign != b_sign) begin
        return a_sign;  // Negative < positive
    end else if (a_sign == 1'b0) begin
        return (a_mag < b_mag);
    end else begin
        return (a_mag > b_mag);
    end
endfunction

wire w_x_lt_min = fp_less_than(i_x, i_min);
wire w_x_gt_max = fp_less_than(i_max, i_x);

// Result selection
assign ow_result = w_any_nan ? i_x :       // Propagate NaN
                   w_x_lt_min ? i_min :    // x < min: return min
                   w_x_gt_max ? i_max :    // x > max: return max
                   i_x;                    // min <= x <= max: return x

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'{name} clamp to [min, max] range',
        generator_script='fp_comparisons.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_all_comparisons(output_path):
    """Generate all comparison modules for all formats."""
    formats = ['fp32', 'fp16', 'bf16', 'fp8_e4m3', 'fp8_e5m2']
    generated = []

    print('\n=== Comparison Operations ===')

    for fmt in formats:
        name = FORMATS[fmt][5]

        # Comparator
        print(f'Generating {name} comparator...')
        module = generate_comparator(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Max
        print(f'Generating {name} max...')
        module = generate_max(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Min
        print(f'Generating {name} min...')
        module = generate_min(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Max Tree (8 elements)
        print(f'Generating {name} max tree...')
        module = generate_max_tree(fmt, output_path, size=8)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Min Tree (8 elements)
        print(f'Generating {name} min tree...')
        module = generate_min_tree(fmt, output_path, size=8)
        generated.append(module)
        print(f'  Created: {module}.sv')

        # Clamp
        print(f'Generating {name} clamp...')
        module = generate_clamp(fmt, output_path)
        generated.append(module)
        print(f'  Created: {module}.sv')

    return generated


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    modules = generate_all_comparisons(output_path)
    print(f'\nGenerated {len(modules)} comparison modules')
