# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP Format Conversions Generator
# Purpose: Generate conversion modules between floating-point formats
#
# Supported formats:
#   - FP32: 1 sign, 8 exp (bias=127), 23 mantissa
#   - FP16: 1 sign, 5 exp (bias=15), 10 mantissa
#   - BF16: 1 sign, 8 exp (bias=127), 7 mantissa
#   - FP8 E4M3: 1 sign, 4 exp (bias=7), 3 mantissa
#   - FP8 E5M2: 1 sign, 5 exp (bias=15), 2 mantissa
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

try:
    from .rtl_header import generate_rtl_header
except ImportError:
    from rtl_generators.ieee754.rtl_header import generate_rtl_header

# Format definitions: (total_bits, exp_bits, mant_bits, bias, has_infinity)
FORMATS = {
    'fp32': (32, 8, 23, 127, True),
    'fp16': (16, 5, 10, 15, True),
    'bf16': (16, 8, 7, 127, True),
    'fp8_e4m3': (8, 4, 3, 7, False),  # No infinity in E4M3
    'fp8_e5m2': (8, 5, 2, 15, True),
}


def generate_upconvert(src_fmt, dst_fmt, output_path):
    """Generate conversion from smaller to larger format (lossless or near-lossless)."""
    src = FORMATS[src_fmt]
    dst = FORMATS[dst_fmt]

    src_bits, src_exp, src_mant, src_bias, src_has_inf = src
    dst_bits, dst_exp, dst_mant, dst_bias, dst_has_inf = dst

    module_name = f'math_{src_fmt}_to_{dst_fmt}'

    # Calculate field positions
    src_sign_pos = src_bits - 1
    src_exp_hi = src_bits - 2
    src_exp_lo = src_mant
    src_mant_hi = src_mant - 1

    dst_sign_pos = dst_bits - 1
    dst_exp_hi = dst_bits - 2
    dst_exp_lo = dst_mant
    dst_mant_hi = dst_mant - 1

    exp_diff = dst_bias - src_bias
    mant_diff = dst_mant - src_mant

    # Max exponent values
    src_exp_max = (1 << src_exp) - 1
    dst_exp_max = (1 << dst_exp) - 1

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{src_bits-1}:0] i_a,
    output logic [{dst_bits-1}:0] ow_result,
    output logic                  ow_invalid
);

// {src_fmt.upper()} field extraction
wire       w_sign = i_a[{src_sign_pos}];
wire [{src_exp-1}:0] w_exp  = i_a[{src_exp_hi}:{src_exp_lo}];
wire [{src_mant-1}:0] w_mant = i_a[{src_mant_hi}:0];

// Special case detection
wire w_is_zero = (w_exp == {src_exp}'h0) & (w_mant == {src_mant}'h0);
wire w_is_subnormal = (w_exp == {src_exp}'h0) & (w_mant != {src_mant}'h0);
'''

    if src_has_inf:
        content += f'''wire w_is_inf = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant == {src_mant}'h0);
wire w_is_nan = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant != {src_mant}'h0);
'''
    else:
        # E4M3 special case: exp=15, mant=7 is NaN
        content += f'''wire w_is_inf = 1'b0;  // {src_fmt.upper()} has no infinity
wire w_is_nan = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant == {src_mant}'h{(1 << src_mant) - 1:X});
'''

    # Handle exponent conversion - only pad if widths differ
    if dst_exp > src_exp:
        content += f'''
// Exponent conversion: add bias difference
// Zero-extend source exponent then add
wire [{dst_exp-1}:0] w_exp_converted = {{{dst_exp - src_exp}'b0, w_exp}} + {dst_exp}'d{exp_diff};
'''
    else:
        content += f'''
// Exponent conversion: add bias difference
wire [{dst_exp-1}:0] w_exp_converted = w_exp + {dst_exp}'d{exp_diff};
'''

    content += f'''
// Mantissa extension: pad with zeros
wire [{dst_mant-1}:0] w_mant_extended = {{w_mant, {mant_diff}'b0}};

// Result assembly
logic [{dst_bits-1}:0] r_result;
logic r_invalid;

always_comb begin
    r_result = {{w_sign, w_exp_converted, w_mant_extended}};
    r_invalid = 1'b0;

    if (w_is_nan) begin
        // Propagate as quiet NaN
        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{1 << (dst_mant-1):X}}};
        r_invalid = 1'b1;
    end else if (w_is_inf) begin
        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h0}};
'''

    if not dst_has_inf:
        content += f'''    end else if (w_is_inf) begin
        // Target format has no infinity - saturate to max
        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{(1 << dst_mant) - 2:X}}};
'''

    content += f'''    end else if (w_is_zero | w_is_subnormal) begin
        // Flush subnormals to zero
        r_result = {{w_sign, {dst_exp}'h0, {dst_mant}'h0}};
    end
end

assign ow_result = r_result;
assign ow_invalid = r_invalid;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'Convert {src_fmt.upper()} to {dst_fmt.upper()} (upconvert)',
        generator_script='fp_conversions.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_downconvert(src_fmt, dst_fmt, output_path):
    """Generate conversion from larger to smaller format (with rounding)."""
    src = FORMATS[src_fmt]
    dst = FORMATS[dst_fmt]

    src_bits, src_exp, src_mant, src_bias, src_has_inf = src
    dst_bits, dst_exp, dst_mant, dst_bias, dst_has_inf = dst

    module_name = f'math_{src_fmt}_to_{dst_fmt}'

    # Calculate field positions
    src_sign_pos = src_bits - 1
    src_exp_hi = src_bits - 2
    src_exp_lo = src_mant
    src_mant_hi = src_mant - 1

    dst_exp_max = (1 << dst_exp) - 1
    src_exp_max = (1 << src_exp) - 1

    exp_diff = src_bias - dst_bias
    mant_diff = src_mant - dst_mant

    # Calculate overflow/underflow thresholds
    # Max representable exponent in dst after bias conversion
    # For formats WITH infinity: exp_max is reserved for inf/nan, so max normal is exp_max-1
    # For formats WITHOUT infinity (E4M3): exp_max is valid (only exp_max with mant=all_ones is NaN)
    if dst_has_inf:
        max_normal_exp = dst_exp_max - 1
    else:
        max_normal_exp = dst_exp_max  # E4M3: exp=15 with mant=0-6 are valid
    max_dst_exp_in_src = max_normal_exp + exp_diff
    min_dst_exp_in_src = 1 + exp_diff  # Minimum normal exponent

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{src_bits-1}:0] i_a,
    output logic [{dst_bits-1}:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// {src_fmt.upper()} field extraction
wire       w_sign = i_a[{src_sign_pos}];
wire [{src_exp-1}:0] w_exp  = i_a[{src_exp_hi}:{src_exp_lo}];
wire [{src_mant-1}:0] w_mant = i_a[{src_mant_hi}:0];

// Special case detection
wire w_is_zero = (w_exp == {src_exp}'h0) & (w_mant == {src_mant}'h0);
wire w_is_subnormal = (w_exp == {src_exp}'h0) & (w_mant != {src_mant}'h0);
wire w_is_inf = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant == {src_mant}'h0);
wire w_is_nan = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant != {src_mant}'h0);

// Exponent conversion with overflow/underflow detection
wire signed [{src_exp+1}:0] w_exp_adjusted = $signed({{2'b0, w_exp}}) - {src_exp+2}'sd{exp_diff};

wire w_exp_overflow = ~w_exp_adjusted[{src_exp+1}] & (w_exp_adjusted > {src_exp+2}'sd{max_normal_exp});
wire w_exp_underflow = w_exp_adjusted[{src_exp+1}] | (w_exp_adjusted < {src_exp+2}'sd1);

// Mantissa truncation with rounding
wire [{dst_mant-1}:0] w_mant_truncated = w_mant[{src_mant-1}:{src_mant - dst_mant}];
wire w_guard = w_mant[{src_mant - dst_mant - 1}];
'''

    if mant_diff > 1:
        content += f'''wire w_round = w_mant[{src_mant - dst_mant - 2}];
wire w_sticky = |w_mant[{src_mant - dst_mant - 3}:0];
'''
    else:
        content += '''wire w_round = 1'b0;
wire w_sticky = 1'b0;
'''

    content += f'''
// RNE rounding
wire w_lsb = w_mant_truncated[0];
wire w_round_up = w_guard & (w_round | w_sticky | w_lsb);

wire [{dst_mant}:0] w_mant_rounded = {{1'b0, w_mant_truncated}} + {{{dst_mant}'b0, w_round_up}};
wire w_mant_overflow = w_mant_rounded[{dst_mant}];

// Final exponent with rounding adjustment
wire [{dst_exp-1}:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[{dst_exp-1}:0] + {dst_exp}'d1) : w_exp_adjusted[{dst_exp-1}:0];
wire [{dst_mant-1}:0] w_mant_final = w_mant_overflow ? {dst_mant}'h0 : w_mant_rounded[{dst_mant-1}:0];

// Check for overflow after rounding (but not if underflow - negative exp has garbage low bits)
'''

    # Handle destination format specifics for overflow detection
    if dst_has_inf:
        # For formats WITH infinity: exp >= max means inf/nan territory
        content += f'''wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | (w_exp_final >= {dst_exp}'h{dst_exp_max:X}));
'''
    else:
        # For formats WITHOUT infinity (E4M3): exp=15 with mant=0-6 are valid
        # Only overflow if exp > max (impossible) or would create NaN pattern (exp=max, mant=max)
        content += f'''
// {dst_fmt.upper()} has no infinity - only overflow if result would be NaN pattern
wire w_result_is_nan_pattern = (w_exp_final == {dst_exp}'h{dst_exp_max:X}) & (w_mant_final >= {dst_mant}'h{(1 << dst_mant) - 1:X});
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | w_result_is_nan_pattern);
'''

    content += f'''
// Result assembly
logic [{dst_bits-1}:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {{w_sign, w_exp_final, w_mant_final}};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
        // Propagate as quiet NaN
'''

    if dst_has_inf:
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{1 << (dst_mant-1):X}}};
'''
    else:
        # For E4M3, NaN is exp=15, mant=7
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{(1 << dst_mant) - 1:X}}};
'''

    content += f'''        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
'''

    if dst_has_inf:
        content += f'''        // Overflow to infinity
        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h0}};
'''
    else:
        content += f'''        // {dst_fmt.upper()} has no infinity - saturate to max normal
        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{(1 << dst_mant) - 2:X}}};
'''

    content += f'''        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        // Underflow to zero
        r_result = {{w_sign, {dst_exp}'h0, {dst_mant}'h0}};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'Convert {src_fmt.upper()} to {dst_fmt.upper()} (downconvert with RNE rounding)',
        generator_script='fp_conversions.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_same_size_convert(src_fmt, dst_fmt, output_path):
    """Generate conversion between same-size formats (e.g., FP16 <-> BF16)."""
    src = FORMATS[src_fmt]
    dst = FORMATS[dst_fmt]

    src_bits, src_exp, src_mant, src_bias, src_has_inf = src
    dst_bits, dst_exp, dst_mant, dst_bias, dst_has_inf = dst

    module_name = f'math_{src_fmt}_to_{dst_fmt}'

    src_sign_pos = src_bits - 1
    src_exp_hi = src_bits - 2
    src_exp_lo = src_mant
    src_mant_hi = src_mant - 1

    src_exp_max = (1 << src_exp) - 1
    dst_exp_max = (1 << dst_exp) - 1

    exp_diff = src_bias - dst_bias

    content = f'''`timescale 1ns / 1ps

module {module_name} (
    input  logic [{src_bits-1}:0] i_a,
    output logic [{dst_bits-1}:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// {src_fmt.upper()} field extraction
wire       w_sign = i_a[{src_sign_pos}];
wire [{src_exp-1}:0] w_exp  = i_a[{src_exp_hi}:{src_exp_lo}];
wire [{src_mant-1}:0] w_mant = i_a[{src_mant_hi}:0];

// Special case detection
wire w_is_zero = (w_exp == {src_exp}'h0) & (w_mant == {src_mant}'h0);
wire w_is_subnormal = (w_exp == {src_exp}'h0) & (w_mant != {src_mant}'h0);
wire w_is_inf = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant == {src_mant}'h0);
wire w_is_nan = (w_exp == {src_exp}'h{src_exp_max:X}) & (w_mant != {src_mant}'h0);

// Exponent conversion
'''
    exp_width = max(src_exp, dst_exp) + 2
    pad_width = exp_width - src_exp
    if exp_diff >= 0:
        content += f'''wire signed [{exp_width-1}:0] w_exp_adjusted = $signed({{{pad_width}'b0, w_exp}}) - {exp_width}'sd{exp_diff};
'''
    else:
        content += f'''wire signed [{exp_width-1}:0] w_exp_adjusted = $signed({{{pad_width}'b0, w_exp}}) + {exp_width}'sd{-exp_diff};
'''

    # Check if we need to handle overflow/underflow due to exponent range difference
    # For formats WITH infinity: max normal exp is dst_exp_max - 1
    # For formats WITHOUT infinity (E4M3): exp=15 with mant=0-6 are valid, so max is dst_exp_max
    if dst_has_inf:
        max_normal_exp = dst_exp_max - 1
    else:
        max_normal_exp = dst_exp_max

    if dst_exp < src_exp:
        content += f'''
wire w_exp_overflow = ~w_exp_adjusted[{exp_width-1}] & (w_exp_adjusted > {exp_width}'sd{max_normal_exp});
wire w_exp_underflow = w_exp_adjusted[{exp_width-1}] | (w_exp_adjusted < {exp_width}'sd1);
'''
    else:
        content += '''
wire w_exp_overflow = 1'b0;
wire w_exp_underflow = 1'b0;
'''

    # Handle mantissa conversion
    if dst_mant > src_mant:
        mant_diff = dst_mant - src_mant
        content += f'''
// Mantissa extension
wire [{dst_mant-1}:0] w_mant_converted = {{w_mant, {mant_diff}'b0}};
wire w_mant_overflow = 1'b0;
'''
    elif dst_mant < src_mant:
        mant_diff = src_mant - dst_mant
        content += f'''
// Mantissa truncation with RNE rounding
wire [{dst_mant-1}:0] w_mant_truncated = w_mant[{src_mant-1}:{mant_diff}];
wire w_guard = w_mant[{mant_diff - 1}];
'''
        if mant_diff > 1:
            content += f'''wire w_sticky = |w_mant[{mant_diff - 2}:0];
'''
        else:
            content += '''wire w_sticky = 1'b0;
'''
        content += f'''wire w_lsb = w_mant_truncated[0];
wire w_round_up = w_guard & (w_sticky | w_lsb);
wire [{dst_mant}:0] w_mant_rounded = {{1'b0, w_mant_truncated}} + {{{dst_mant}'b0, w_round_up}};
wire w_mant_overflow = w_mant_rounded[{dst_mant}];
wire [{dst_mant-1}:0] w_mant_converted = w_mant_overflow ? {dst_mant}'h0 : w_mant_rounded[{dst_mant-1}:0];
'''
    else:
        content += f'''
// Same mantissa size
wire [{dst_mant-1}:0] w_mant_converted = w_mant;
wire w_mant_overflow = 1'b0;
'''

    content += f'''
// Final exponent
wire [{dst_exp-1}:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[{dst_exp-1}:0] + {dst_exp}'d1) : w_exp_adjusted[{dst_exp-1}:0];

// Check for final overflow (but not if underflow - negative exp has garbage low bits)
'''

    if dst_has_inf:
        # For formats WITH infinity: exp >= max means inf/nan territory
        content += f'''wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | (w_exp_final >= {dst_exp}'h{dst_exp_max:X}));
'''
    else:
        # For formats WITHOUT infinity (E4M3): only overflow if result would be NaN pattern
        content += f'''
// {dst_fmt.upper()} has no infinity - only overflow if result would be NaN pattern
wire w_result_is_nan_pattern = (w_exp_final == {dst_exp}'h{dst_exp_max:X}) & (w_mant_converted >= {dst_mant}'h{(1 << dst_mant) - 1:X});
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | w_result_is_nan_pattern);
'''

    content += f'''
// Result assembly
logic [{dst_bits-1}:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {{w_sign, w_exp_final, w_mant_converted}};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
'''

    if dst_has_inf:
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{1 << (dst_mant-1):X}}};
'''
    else:
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{(1 << dst_mant) - 1:X}}};
'''

    content += f'''        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
'''

    if dst_has_inf:
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h0}};
'''
    else:
        content += f'''        r_result = {{w_sign, {dst_exp}'h{dst_exp_max:X}, {dst_mant}'h{(1 << dst_mant) - 2:X}}};
'''

    content += f'''        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        r_result = {{w_sign, {dst_exp}'h0, {dst_mant}'h0}};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule
'''

    header = generate_rtl_header(
        module_name=module_name,
        purpose=f'Convert {src_fmt.upper()} to {dst_fmt.upper()}',
        generator_script='fp_conversions.py'
    )

    with open(f'{output_path}/{module_name}.sv', 'w') as f:
        f.write(header + content + '\n')

    return module_name


def generate_conversion(src_fmt, dst_fmt, output_path):
    """Generate appropriate conversion based on format sizes."""
    src = FORMATS[src_fmt]
    dst = FORMATS[dst_fmt]

    src_bits = src[0]
    dst_bits = dst[0]
    src_precision = src[1] + src[2]  # exp + mant bits
    dst_precision = dst[1] + dst[2]

    if src_bits == dst_bits:
        return generate_same_size_convert(src_fmt, dst_fmt, output_path)
    elif dst_precision > src_precision:
        return generate_upconvert(src_fmt, dst_fmt, output_path)
    else:
        return generate_downconvert(src_fmt, dst_fmt, output_path)


def generate_all_conversions(output_path):
    """Generate all conversion modules."""
    formats = ['fp32', 'fp16', 'bf16', 'fp8_e4m3', 'fp8_e5m2']
    generated = []

    print('\n=== FP Format Conversions ===')

    for src in formats:
        for dst in formats:
            if src != dst:
                print(f'Generating {src} -> {dst}...')
                name = generate_conversion(src, dst, output_path)
                generated.append(name)
                print(f'  Created: {name}.sv')

    return generated


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    modules = generate_all_conversions(output_path)
    print(f'\nGenerated {len(modules)} conversion modules')
