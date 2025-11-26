# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HanCarlsonAdder
# Purpose: Han-Carlson Prefix Adder Generator
#
# The Han-Carlson adder is a hybrid prefix adder that combines properties of
# Kogge-Stone (minimum depth) and Brent-Kung (minimum cell count). It achieves:
# - 5 logic levels for 16-bit (vs 4 for Kogge-Stone)
# - 39 prefix cells (vs 64 for Kogge-Stone)
# - Constant fanout of 2 (vs exponential for Sklansky)
# - 4 wiring tracks (vs 8 for Kogge-Stone)
#
# This makes it optimal for advanced process nodes (5nm+) where wire delay
# dominates and routing congestion must be minimized.
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

import math
from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class HanCarlsonAdder(Module):
    """
    Generates a Han-Carlson prefix adder for optimal 16-bit CPA.

    Han-Carlson structure:
    - Stage 1: Kogge-Stone style (all even positions)
    - Stages 2-4: Brent-Kung style (parallel prefix)
    - Stage 5: Ripple for odd positions from even neighbors

    For 16-bit:
    - 5 logic levels (depth)
    - ~39 prefix cells
    - Fanout = 2 (constant)
    - 4 wiring tracks
    """

    module_str = 'math_adder_han_carlson'
    param_str = 'parameter int N=16'
    port_str = '''
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_cin,
    output logic [N-1:0] ow_sum,
    output logic         ow_cout
    '''

    def __init__(self, width):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.width = width
        self.module_name = f'{self.module_name}_{str(self.width).zfill(3)}'
        self.params.set_param_value('N', self.width)
        self.num_stages = math.ceil(math.log2(width)) + 1  # Han-Carlson needs +1 stage

    def generate_pg_computation(self):
        """Generate initial propagate (P) and generate (G) signals."""
        N = self.width
        self.comment('Stage 0: Initial P and G computation')
        self.instruction(f'logic [N-1:0] w_p0, w_g0;')
        self.instruction('')

        self.comment('P = A XOR B, G = A AND B')
        self.instruction('genvar i;')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < N; i++) begin : gen_pg')
        self.instruction('        assign w_p0[i] = i_a[i] ^ i_b[i];')
        self.instruction('        assign w_g0[i] = i_a[i] & i_b[i];')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

    def generate_han_carlson_tree(self):
        """
        Generate the Han-Carlson prefix tree.

        Han-Carlson is a sparsity-2 prefix network:
        1. First stage: Combine adjacent pairs on even positions (G[i:i-1])
        2. Middle stages: Kogge-Stone style on even positions only
        3. Final stage: Odd positions get carries from even neighbors

        For 16-bit: stages work on even positions 0,2,4,6,8,10,12,14
        - Stage 1: Each even pos combines with previous odd (span 2)
        - Stage 2: Span 4 (combine with position -2)
        - Stage 3: Span 8 (combine with position -4)
        - Stage 4: Span 16 (combine with position -8)
        - Stage 5: Fill odd positions
        """
        N = self.width
        num_stages = self.num_stages

        self.comment('Han-Carlson prefix tree')
        self.comment('Sparsity-2: compute even positions first, then fill odd positions')
        self.instruction('')

        # Declare stage arrays
        for stage in range(1, num_stages + 1):
            self.instruction(f'logic [N-1:0] w_p{stage}, w_g{stage};')
        self.instruction('')

        # Stage 1: Initial span-2 prefix on even positions
        # Creates G[i:i-1] for even i, where G[0:-1] includes cin
        self.comment('Stage 1: Span-2 prefix (even positions combine with odd neighbor)')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < N; i++) begin : gen_stage1')
        self.instruction('        if (i == 0) begin : gen_s1_bit0')
        self.instruction('            // Bit 0: incorporate carry-in (G[0:-1])')
        self.instruction('            assign w_g1[0] = w_g0[0] | (w_p0[0] & i_cin);')
        self.instruction('            assign w_p1[0] = w_p0[0];')
        self.instruction('        end else if (i % 2 == 0) begin : gen_s1_even')
        self.instruction('            // Even positions: G[i:i-1] = G[i] | P[i] & G[i-1]')
        self.instruction('            math_prefix_cell u_pf_s1 (')
        self.instruction('                .i_g_hi(w_g0[i]),   .i_p_hi(w_p0[i]),')
        self.instruction('                .i_g_lo(w_g0[i-1]), .i_p_lo(w_p0[i-1]),')
        self.instruction('                .ow_g(w_g1[i]),     .ow_p(w_p1[i])')
        self.instruction('            );')
        self.instruction('        end else begin : gen_s1_odd')
        self.instruction('            // Odd positions: pass through (will be filled in final stage)')
        self.instruction('            assign w_g1[i] = w_g0[i];')
        self.instruction('            assign w_p1[i] = w_p0[i];')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

        # Stages 2 to num_stages-1: Kogge-Stone style on even positions
        # Each stage doubles the span: 4, 8, 16, ...
        for stage in range(2, num_stages):
            span = 2 ** stage  # span = 4, 8, 16, ...
            step = span // 2   # step = 2, 4, 8, ... (distance to lower operand)
            self.comment(f'Stage {stage}: Kogge-Stone on even positions (span {span}, step {step})')
            self.instruction('generate')
            self.instruction(f'    for (i = 0; i < N; i++) begin : gen_stage{stage}')
            # Active for even positions where we have a valid lower operand
            # Even position i combines with even position (i - step) if (i - step) >= 0
            self.instruction(f'        if (i % 2 == 0 && i >= {step}) begin : gen_s{stage}_active')
            self.instruction(f'            math_prefix_cell u_pf_s{stage} (')
            self.instruction(f'                .i_g_hi(w_g{stage-1}[i]),       .i_p_hi(w_p{stage-1}[i]),')
            self.instruction(f'                .i_g_lo(w_g{stage-1}[i-{step}]), .i_p_lo(w_p{stage-1}[i-{step}]),')
            self.instruction(f'                .ow_g(w_g{stage}[i]),           .ow_p(w_p{stage}[i])')
            self.instruction('            );')
            self.instruction(f'        end else begin : gen_s{stage}_pass')
            self.instruction(f'            assign w_g{stage}[i] = w_g{stage-1}[i];')
            self.instruction(f'            assign w_p{stage}[i] = w_p{stage-1}[i];')
            self.instruction('        end')
            self.instruction('    end')
            self.instruction('endgenerate')
            self.instruction('')

        # Final stage: Fill in odd positions from even neighbors
        # Odd position i gets carry from even position i-1
        final_stage = num_stages
        self.comment(f'Stage {final_stage}: Fill odd positions (from even neighbors)')
        self.instruction('generate')
        self.instruction(f'    for (i = 0; i < N; i++) begin : gen_stage{final_stage}')
        self.instruction(f'        if (i % 2 == 1) begin : gen_s{final_stage}_odd')
        self.instruction('            // Odd positions: G[i:-1] = G[i] | P[i] & G[i-1:-1]')
        self.instruction(f'            math_prefix_cell_gray u_pf_s{final_stage} (')
        self.instruction(f'                .i_g_hi(w_g{final_stage-1}[i]), .i_p_hi(w_p{final_stage-1}[i]),')
        self.instruction(f'                .i_g_lo(w_g{final_stage-1}[i-1]),')
        self.instruction(f'                .ow_g(w_g{final_stage}[i])')
        self.instruction('            );')
        self.instruction(f'            assign w_p{final_stage}[i] = w_p{final_stage-1}[i];')
        self.instruction(f'        end else begin : gen_s{final_stage}_even')
        self.instruction(f'            assign w_g{final_stage}[i] = w_g{final_stage-1}[i];')
        self.instruction(f'            assign w_p{final_stage}[i] = w_p{final_stage-1}[i];')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

    def generate_sum_computation(self):
        """Generate final sum computation."""
        N = self.width
        final_stage = self.num_stages

        self.comment('Final sum computation')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < N; i++) begin : gen_sum')
        self.instruction('        if (i == 0) begin : gen_sum_bit0')
        self.instruction('            assign ow_sum[0] = w_p0[0] ^ i_cin;')
        self.instruction('        end else begin : gen_sum_other')
        self.instruction(f'            assign ow_sum[i] = w_p0[i] ^ w_g{final_stage}[i-1];')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

        self.comment('Carry out')
        self.instruction(f'assign ow_cout = w_g{final_stage}[N-1];')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete Han-Carlson adder."""
        self.generate_pg_computation()
        self.generate_han_carlson_tree()
        self.generate_sum_computation()

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose=f'Han-Carlson {self.width}-bit prefix adder for BF16 final CPA',
            generator_script='han_carlson_adder.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_han_carlson_adder(width, output_path):
    """
    Generate a Han-Carlson prefix adder of specified width.

    Args:
        width: Bit width of the adder (typically 16 for BF16)
        output_path: Directory to write the generated file
    """
    adder = HanCarlsonAdder(width)
    adder.verilog(output_path)
    return adder.module_name


if __name__ == '__main__':
    import sys
    import os

    # Default to 16-bit for BF16
    width = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    output_path = sys.argv[2] if len(sys.argv) > 2 else '.'

    module_name = generate_han_carlson_adder(width, output_path)
    print(f'Generated: {module_name}.sv')
