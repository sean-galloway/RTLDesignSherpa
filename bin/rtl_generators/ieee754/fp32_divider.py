# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32Divider
# Purpose: Complete IEEE 754-2008 FP32 Divider Generator
#
# Implements a latency-optimized IEEE 754-2008 single-precision divider:
#   a/b = a * (1/b), 1/b refined by Newton iteration, quotient corrected
#   through an EXACT integer residual so the final rounding is textbook RNE
#   with TRUE (unfolded) sticky -- not a bounded-ulp approximation.
#
# Algorithm (Goldschmidt-class multiplicative divide, latency-optimized):
#   1. Reciprocal seed r0 from a 7-bit-index / 12-bit-entry LUT over the
#      divisor significand (B[22:16]). Bucket-center design, saturated:
#      measured |r0*b - 1| <= 2^-7.96 across every bucket end.
#   2. Two Newton refinements r' = r*(2 - b*r) on the 24x24 family
#      significand multiplier. Exhaustively verified over ALL 2^24 divisors
#      at generate time: |B*r2 - 2^47| <= 24992532 (rel <= 2^-22.5).
#   3. q0 = a*r2, biased down by 8 significand-LSBs so the EXACT integer
#      residual rem = a' - B*q0 (a' = a<<(23+half)) lands in [0, 16*B).
#      The bias makes q0 <= true significand; the measured Newton error
#      (<= 5.96 S units) plus bias keeps rem inside one 4-bit reduction.
#   4. Final rounding is EXACT: rem = k*B + remp (k in 0..15 binary chain),
#      q_base = q0 + k, round up iff (2*remp > B) | ((2*remp == B) & LSB)
#      -- textbook RNE, TRUE sticky, with the residual known exactly. No
#      last-bit faithfulness gap is possible by construction.
#   Latency: 9 cycles from the accept edge to ow_valid on the normal
#   path (10 counting the cycle i_valid is presented); exact subnormal-grid
#   results take 10 (11 with accept) for the m*B compare cycle; special
#   cases complete in 1 cycle (2 with accept).
#
# FP32 Format (IEEE 754-2008):
#   [31]    - Sign bit
#   [30:23] - 8-bit biased exponent (bias = 127)
#   [22:0]  - 23-bit mantissa (implied leading 1 for normalized)
#
# Subnormal handling:
#   SUBNORMAL_SUPPORT=0 (default): FTZ. Subnormal operands are treated as
#     zero (x/0, 0/x, 0/0 rules) and quotients are never subnormal: any
#     quotient with pre-round exponent <= 0 flushes to signed zero with
#     ow_underflow (matches the multiplier slice's =0 flag semantics).
#   SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow. Subnormal
#     operands are normalized into [1,2) with exponent bookkeeping
#     (effective exponent k-22); subnormal quotients land on the exact
#     subnormal grid via a right shift of the corrected significand with
#     dropped-bit sticky folded into TRUE sticky. A rounding carry out of
#     pre-round exponent 0 yields min-normal, not a flush (math BUG-004
#     ruling); ow_underflow asserts exactly when the after-rounding result
#     is tiny (exp field 0) AND the quotient was inexact.
#
# Special cases (IEEE 754-2008):
#   - NaN in (either operand): canonical qNaN out, ow_invalid set
#   - 0/0, inf/inf: canonical qNaN out, ow_invalid set
#   - x/0 (x nonzero): +/-inf, no invalid
#   - 0/x, x/inf: signed zero
#   - inf/x: +/-inf
#   - sign = sa ^ sb on every non-NaN result
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header

# Reciprocal seed LUT: 7-bit index (divisor significand B[22:16]), 12-bit
# entries, entry saturated at 4095 so R0 = entry<<12 stays below 2^24.
LUT_INDEX_BITS = 7
LUT_DATA_BITS = 12


def _build_reciprocal_lut():
    """Exact-integer bucket-center reciprocal LUT (same construction the
    module documents)."""
    lut = []
    for idx in range(1 << LUT_INDEX_BITS):
        # bucket center: 2^23 + (idx + 0.5) * 2^(23-LUT_INDEX_BITS), exact
        b_center = (1 << 23) + ((2 * idx + 1) << (22 - LUT_INDEX_BITS))
        num = (1 << 23) << LUT_DATA_BITS        # 2^23 * 2^12
        r = num // b_center
        if (num - r * b_center) * 2 >= b_center:
            r += 1                              # round to nearest
        if r >= (1 << LUT_DATA_BITS):           # saturate: keeps R0 < 2^24
            r = (1 << LUT_DATA_BITS) - 1
        lut.append(r)
    return lut


RECIPROCAL_LUT = _build_reciprocal_lut()


def _newton_refine(b, r):
    """One Newton refinement, bit-faithful to the generated datapath.

    Products go through the significand multiplier: operands enter as
    {i_is_normal, i_mant} = {bit 23, bits 22:0} of the 24-bit value, so
    any operand below 2^23 (the Newton factor e can be) keeps its true
    hidden bit instead of gaining a phantom one.
    """
    t = (b * r) >> 24  # both operands >= 2^23: reconstruction is identity here
    e = (1 << 24) - t
    rn = (_mult_recon(r, e) + (1 << 22)) >> 23
    if rn >= (1 << 24):
        rn = (1 << 24) - 1
    return rn


def _mult_recon(x, y):
    """The significand multiplier's {hidden, mant[22:0]} reconstruction."""
    return ((x >> 23) << 23 | (x & 0x7FFFFF)) * ((y >> 23) << 23 | (y & 0x7FFFFF))


def verify_accuracy_bounds(lut=None):
    """Generate-time proof obligations for the exact-rounding scheme.

    Returns (seed_worst, r2_worst) where both are max |B*r - 2^47| values.
    Raises AssertionError if the exactness preconditions fail:
      - seed error stays in the documented 2^-8 class (checked at every
        bucket end, where |R0*B - 2^47| is maximal within a bucket)
      - after two Newton refinements the worst |B*r2 - 2^47| over ALL 2^24
        divisors keeps the residual inside one 4-bit reduction together
        with the 8-S-unit bias:  2*worst + 9*2^23 < 16*2^23.
    """
    lut = RECIPROCAL_LUT if lut is None else lut

    seed_worst = 0
    for idx in range(1 << LUT_INDEX_BITS):
        r0 = lut[idx] << 12
        base = (1 << 23) + idx * (1 << (23 - LUT_INDEX_BITS))
        for low in (0, 1, (1 << (23 - LUT_INDEX_BITS)) // 2,
                    (1 << (23 - LUT_INDEX_BITS)) - 1):
            b = base + low
            if b >= (1 << 24):
                continue
            err = abs(r0 * b - (1 << 47))
            seed_worst = max(seed_worst, err)
    # 2^-8 class: allow a little slack over the measured 2^39.6
    assert seed_worst < (1 << 42), f'seed error {seed_worst} out of 2^-8 class'

    r2_worst = 0
    for b in range(1 << 23, 1 << 24):
        r0 = lut[(b >> (23 - LUT_INDEX_BITS)) & ((1 << LUT_INDEX_BITS) - 1)] << 12
        r1 = _newton_refine(b, r0)
        r2 = _newton_refine(b, r1)
        err = abs(b * r2 - (1 << 47))
        if err > r2_worst:
            r2_worst = err

    # Exact-residual invariant: q0 error (<= 2*r2_worst/2^23 S units, half=1)
    # plus the 8-S-unit bias plus one trunc unit must stay under 16 B.
    assert 2 * r2_worst + 9 * (1 << 23) < 16 * (1 << 23), \
        f'Newton error {r2_worst} breaks the 4-bit residual reduction'
    return seed_worst, r2_worst


class FP32Divider(Module):
    """
    Generates the complete IEEE 754-2008 FP32 divider.

    Architecture (multi-cycle FSM, one 24x24 significand multiply per cycle):
    1. Accept: classify operands, capture normalized significands/exponents,
       route special cases straight to the output register.
    2. S_LUT:   reciprocal seed from the 7-bit index LUT.
    3. S_NR1A/S_NR1B: Newton refine #1 (two significand multiplies).
    4. S_NR2A/S_NR2B: Newton refine #2 (exhaustively bounded at generate time).
    5. S_Q0:    q0 = A*r2, biased down 8 significand LSBs.
    6. S_REM:   exact residual rem = A<<(23+half) - B*q0, in [0, 16B).
    7. S_RNE:   exact 4-bit reduction + textbook RNE with TRUE sticky;
       exponent assembly, subnormal grid shift, under/overflow flags.
    """

    module_str = 'math_ieee754_2008_fp32_divider'
    port_str = '''
    input  logic        i_clk,          // System clock
    input  logic        i_rst_n,        // Active-low async reset
    input  logic [31:0] i_a,            // FP32 dividend
    input  logic [31:0] i_b,            // FP32 divisor
    input  logic        i_valid,        // Input valid (single cycle)
    output logic [31:0] ow_result,      // FP32 quotient
    output logic        ow_overflow,    // Overflow to infinity
    output logic        ow_underflow,   // Underflow (tiny after rounding, inexact)
    output logic        ow_invalid,     // Invalid operation (NaN result)
    output logic        ow_valid        // Output valid (single cycle)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_parameter(self):
        """Inject the SUBNORMAL_SUPPORT parameter into the module header."""
        header = self.start_instructions[0]
        old = f'module {self.module_name}(\n'
        new = (f'module {self.module_name} #(\n'
               "    parameter bit SUBNORMAL_SUPPORT = 1'b0  "
               "// 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow\n) (\n")
        if old not in header:
            raise RuntimeError(f'module header patch failed for {self.module_name}')
        self.start_instructions[0] = header.replace(old, new, 1)

    def generate_fsm_states(self):
        self.comment('FSM states: iterative, one multiply per cycle')
        self.instruction("localparam logic [3:0] S_IDLE  = 4'd0,")
        self.instruction("                       S_LUT   = 4'd1,")
        self.instruction("                       S_NR1A  = 4'd2,")
        self.instruction("                       S_NR1B  = 4'd3,")
        self.instruction("                       S_NR2A  = 4'd4,")
        self.instruction("                       S_NR2B  = 4'd5,")
        self.instruction("                       S_Q0    = 4'd6,")
        self.instruction("                       S_REM   = 4'd7,")
        self.instruction("                       S_RNE   = 4'd8,")
        self.instruction("                       S_OUT   = 4'd9,")
        self.instruction("                       S_SUBN  = 4'd10;")
        self.instruction('')

    def generate_input_decode(self):
        """Combinatorial operand decode/preparation straight from the inputs.

        Sampled at the accept edge: normalized 24-bit significands with
        hidden bit, signed effective exponents (subnormal operands normalize
        at exponent k-22 when SUBNORMAL_SUPPORT=1), sign, and the special
        classification. Identical logic feeds the special-case output mux.
        """
        self.comment('Input field extraction (combinatorial, sampled at accept)')
        self.comment('Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa')
        self.instruction('')
        self.instruction('wire        w_sign_a = i_a[31];')
        self.instruction('wire [7:0]  w_exp_a  = i_a[30:23];')
        self.instruction('wire [22:0] w_mant_a = i_a[22:0];')
        self.instruction('')
        self.instruction('wire        w_sign_b = i_b[31];')
        self.instruction('wire [7:0]  w_exp_b  = i_b[30:23];')
        self.instruction('wire [22:0] w_mant_b = i_b[22:0];')
        self.instruction('')
        self.comment('Special value detection')
        self.instruction('')
        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h000000);")
        self.instruction('')
        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h000000);")
        self.instruction('')
        self.comment('Infinity: exp=FF, mant=0')
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h000000);")
        self.instruction('')
        self.comment('NaN: exp=FF, mant!=0')
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h000000);")
        self.instruction('')
        self.comment('Effective zero: FTZ folds subnormals into zero; with')
        self.comment('SUBNORMAL_SUPPORT=1 only true zeros are effective zero')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('')
        self.comment('Result sign: XOR of input signs (all non-NaN results)')
        self.instruction('wire w_sign_result = w_sign_a ^ w_sign_b;')
        self.instruction('')

    def generate_special_case_logic(self):
        """Special-case classification and result values (sampled at accept)."""
        self.comment('IEEE 754-2008 special cases (priority order)')
        self.comment('NaN in -> canonical qNaN + invalid; 0/0 and inf/inf -> qNaN + invalid;')
        self.comment('x/0 -> inf; 0/x -> zero; inf/x -> inf; x/inf -> zero')
        self.comment('Declared here (before first use); assigned in the mux below')
        self.instruction('reg [31:0] w_spec_result;')
        self.instruction('reg        w_spec_invalid;')
        self.instruction('')
        self.instruction('wire w_any_nan   = w_a_is_nan | w_b_is_nan;')
        self.instruction('wire w_zero_zero = w_a_eff_zero & w_b_eff_zero;')
        self.instruction('wire w_inf_inf   = w_a_is_inf & w_b_is_inf;')
        self.instruction('wire w_is_special = w_any_nan | w_zero_zero | w_inf_inf |')
        self.instruction('    w_a_eff_zero | w_b_eff_zero | w_a_is_inf | w_b_is_inf;')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    w_spec_result  = {w_sign_result, 8\'h00, 23\'h000000};')
        self.instruction('    w_spec_invalid = 1\'b0;')
        self.instruction("    if (w_any_nan | w_zero_zero | w_inf_inf) begin")
        self.instruction('        w_spec_result  = {w_sign_result, 8\'hFF, 23\'h400000};')
        self.instruction("        w_spec_invalid = 1'b1;")
        self.instruction('    end else if (w_b_eff_zero | w_a_is_inf) begin')
        self.instruction("        w_spec_result = {w_sign_result, 8'hFF, 23'h000000};")
        self.instruction('    end')
        self.comment('    remaining cases (w_a_eff_zero | w_b_is_inf) -> signed zero by default')
        self.instruction('end')
        self.instruction('')

    def generate_operand_preparation(self):
        """Normalized significands and effective exponents for the datapath.

        Subnormal operands (SUBNORMAL_SUPPORT=1) are left-normalized into
        [1,2) with the hidden bit set and the effective exponent debited by
        the shift amount: value = 0.m * 2^(1-bias) = (m<<(23-k)) * 2^((k-22)-bias).
        """
        self.comment('-' * 73)
        self.comment('Operand preparation: 24-bit significands, signed effective')
        self.comment('exponents. At SUBNORMAL_SUPPORT=1 a subnormal operand is')
        self.comment('left-normalized into [1,2) with exponent debit k-22; at =0')
        self.comment('subnormals never reach this path (effective zero routed to')
        self.comment('the special cases).')
        self.comment('-' * 73)
        self.instruction('')
        self.comment('Left-shift amount for a subnormal operand: 23 - leading-bit-pos,')
        self.comment('last assignment wins (loop keeps the highest set bit)')
        self.instruction('logic [4:0] r_a_sub_shift;')
        self.instruction('logic [4:0] r_b_sub_shift;')
        self.instruction('always_comb begin')
        self.instruction("    r_a_sub_shift = 5'd0;")
        self.instruction('    for (int i = 0; i < 23; i++) begin')
        self.instruction("        if (w_mant_a[i]) r_a_sub_shift = 5'd23 - 5'(i);")
        self.instruction('    end')
        self.instruction("    r_b_sub_shift = 5'd0;")
        self.instruction('    for (int i = 0; i < 23; i++) begin')
        self.instruction("        if (w_mant_b[i]) r_b_sub_shift = 5'd23 - 5'(i);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.comment('Significands with hidden bit: subnormal operand = {1\'b0, mant} << shift')
        self.instruction('wire [23:0] w_sig_a_norm = {1\'b0, w_mant_a} << r_a_sub_shift;')
        self.instruction('wire [23:0] w_sig_b_norm = {1\'b0, w_mant_b} << r_b_sub_shift;')
        self.instruction("wire [23:0] w_sig_a = SUBNORMAL_SUPPORT & w_a_is_subnormal ?")
        self.instruction("    w_sig_a_norm : {1'b1, w_mant_a};")
        self.instruction("wire [23:0] w_sig_b = SUBNORMAL_SUPPORT & w_b_is_subnormal ?")
        self.instruction("    w_sig_b_norm : {1'b1, w_mant_b};")
        self.instruction('')
        self.comment('Effective biased exponents: subnormal operates at 1 - shift')
        self.instruction("wire signed [9:0] w_ea_sub = 10'sd1 - $signed({5'b00000, r_a_sub_shift});")
        self.instruction("wire signed [9:0] w_eb_sub = 10'sd1 - $signed({5'b00000, r_b_sub_shift});")
        self.instruction("wire signed [9:0] w_ea_s = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ?")
        self.instruction('    w_ea_sub : $signed({2\'b00, w_exp_a});')
        self.instruction("wire signed [9:0] w_eb_s = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ?")
        self.instruction('    w_eb_sub : $signed({2\'b00, w_exp_b});')
        self.instruction('')
        self.comment('Quotient significand ratio < 1: debit one exponent, track via r_half')
        self.instruction('wire w_half = (w_sig_a < w_sig_b);')
        self.instruction('')

    def generate_reciprocal_lut(self):
        """Emit the 128-entry reciprocal seed LUT as a case statement."""
        self.comment('-' * 73)
        self.comment(f'Reciprocal seed LUT: {LUT_INDEX_BITS}-bit index (divisor')
        self.comment(f'significand B[22:16]), {LUT_DATA_BITS}-bit bucket-center entries,')
        self.comment('saturated so R0 = entry<<12 stays below 2^24. Measured')
        self.comment('|r0*b - 1| <= 2^-7.96 at every bucket end; two Newton')
        self.comment('refinements follow (exhaustively bounded at generate time).')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction(f'logic [{LUT_DATA_BITS-1}:0] r_lut_val;')
        self.comment('Index mux: divisor is live at accept, registered afterwards')
        self.instruction(f'wire [{LUT_INDEX_BITS-1}:0] w_lut_idx =')
        self.instruction("    (r_state == S_IDLE) ? w_sig_b[22:16] : r_b24[22:16];")
        self.instruction('always_comb begin')
        self.instruction('    case (w_lut_idx)')
        for idx, entry in enumerate(RECIPROCAL_LUT):
            self.instruction(f"        {LUT_INDEX_BITS}'d{idx}: r_lut_val = "
                             f"{LUT_DATA_BITS}'h{entry:03X};")
        self.instruction("        default: r_lut_val = 12'h000;")
        self.instruction('    endcase')
        self.instruction('end')
        self.instruction('')

    def generate_multiply_unit(self):
        """The single shared 24x24 significand multiplier (one use per cycle)."""
        self.comment('-' * 73)
        self.comment('Shared significand multiplier: one 24x24 Dadda multiply per')
        self.comment('FSM cycle (Newton factors, q0, and the exact residual all')
        self.comment('reuse this instance). i_*_is_normal IS the operand hidden')
        self.comment('bit, so each operand presents its own bit 23 (see below).')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction('logic [22:0] w_mult_a;')
        self.instruction('logic [22:0] w_mult_b;')
        self.instruction('wire [47:0] w_prod;')
        self.comment('w_m drives the S_RNE A-port hidden bit; declared here')
        self.comment('(before the instantiation) and assigned in S_RNE logic.')
        self.instruction('wire [23:0] w_m;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp32_mantissa_mult u_mant_mult (')
        self.instruction('    .i_mant_a(w_mult_a),')
        self.instruction('    .i_mant_b(w_mult_b),')
        self.comment('    hidden-bit semantics per operand: i_*_is_normal IS the')
        self.comment('    operand hidden bit, so EVERY state presents its own')
        self.comment('    bit 23. The refined r1 (measured as low as 0x7FFFE1),')
        self.comment('    the Newton factors e1/e2, the biased q0, and the')
        self.comment('    subnormal-grid m can all dip below 2^23; a hardwired 1')
        self.comment('    would graft a phantom hidden bit onto them and corrupt')
        self.comment('    the exact residual. The exhaustive Newton proof in')
        self.comment('    verify_accuracy_bounds assumes exactly this')
        self.comment('    reconstruction (plain 24x24 products).')
        self.instruction("    .i_a_is_normal((r_state == S_RNE)  ? w_m[23]   :")
        self.instruction("                   (r_state == S_NR1B) ? r_r0[23]  :")
        self.instruction("                   (r_state == S_NR2B) ? r_r1[23]  :")
        self.instruction("                   (r_state == S_Q0)   ? r_a24[23] : 1'b1),")
        self.instruction("    .i_b_is_normal((r_state == S_REM)  ? r_q0[23]  :")
        self.instruction("                   (r_state == S_NR1B) ? w_e1[23]  :")
        self.instruction("                   (r_state == S_NR2B) ? w_e2[23]  :")
        self.instruction("                   (r_state == S_NR1A) ? r_r0[23]  :")
        self.instruction("                   (r_state == S_NR2A) ? r_r1[23]  :")
        self.instruction("                   (r_state == S_Q0)   ? r_r2[23]  : 1'b1),")
        self.instruction('    .ow_product(w_prod),')
        self.instruction('    .ow_needs_norm(),')
        self.instruction('    .ow_mant_out(),')
        self.instruction('    .ow_guard_bit(),')
        self.instruction('    .ow_round_bit(),')
        self.instruction('    .ow_sticky_bit()')
        self.instruction(');')
        self.instruction('')
        self.comment('Multiplier operand mux (registered values only)')
        self.instruction('always_comb begin')
        self.instruction("    w_mult_a = 23'h000000;")
        self.instruction("    w_mult_b = 23'h000000;")
        self.instruction('    case (r_state)')
        self.instruction('        S_NR1A: begin')
        self.instruction('            w_mult_a = r_b24[22:0];')
        self.instruction('            w_mult_b = r_r0[22:0];')
        self.instruction('        end')
        self.instruction('        S_NR1B: begin')
        self.instruction('            w_mult_a = r_r0[22:0];')
        self.instruction('            w_mult_b = w_e1[22:0];')
        self.instruction('        end')
        self.instruction('        S_NR2A: begin')
        self.instruction('            w_mult_a = r_b24[22:0];')
        self.instruction('            w_mult_b = r_r1[22:0];')
        self.instruction('        end')
        self.instruction('        S_NR2B: begin')
        self.instruction('            w_mult_a = r_r1[22:0];')
        self.instruction('            w_mult_b = w_e2[22:0];')
        self.instruction('        end')
        self.instruction('        S_Q0: begin')
        self.instruction('            w_mult_a = r_a24[22:0];')
        self.instruction('            w_mult_b = r_r2[22:0];')
        self.instruction('        end')
        self.instruction('        S_REM: begin')
        self.instruction('            w_mult_a = r_b24[22:0];')
        self.instruction('            w_mult_b = r_q0[22:0];')
        self.instruction('        end')
        self.instruction('        S_RNE: begin')
        self.comment('            subnormal-grid prep: m * B (exact residual fraction)')
        self.instruction('            w_mult_a = w_m[22:0];')
        self.instruction('            w_mult_b = r_b24[22:0];')
        self.instruction('        end')
        self.instruction('        default: begin')
        self.instruction("            w_mult_a = 23'h000000;")
        self.instruction("            w_mult_b = 23'h000000;")
        self.instruction('        end')
        self.instruction('    endcase')
        self.instruction('end')
        self.instruction('')

    def generate_datapath_registers(self):
        """Datapath registers and the Newton-stage wiring."""
        self.comment('Registered operands and datapath state')
        self.instruction('logic [3:0]   r_state;')
        self.instruction('logic [23:0]  r_a24, r_b24;')
        self.instruction('logic signed [9:0] r_ea_s, r_eb_s;')
        self.instruction('logic         r_sign, r_half;')
        self.instruction('logic [23:0]  r_r0, r_t1, r_r1, r_t2, r_r2, r_q0;')
        self.instruction('logic [27:0]  r_rem;')
        self.instruction('logic [47:0]  r_mprod;   // S_RNE: exact m*B for the grid compare')
        self.instruction('logic [27:0]  r_red;     // S_RNE: exact residual remainder')
        self.instruction('logic [23:0]  r_qbase;   // S_RNE: exact quotient integer part')
        self.instruction('logic [4:0]   r_sh;      // S_RNE: subnormal grid shift')
        self.instruction('logic [31:0]  r_result;')
        self.instruction('logic         r_overflow, r_underflow, r_invalid, r_owv;')
        self.instruction('')
        self.comment('Newton factors: e = 2 - t, t = trunc(B*r) at 2^-23')
        self.instruction('wire [24:0] w_e1_full = 25\'h1000000 - {1\'b0, r_t1};')
        self.instruction('wire [24:0] w_e2_full = 25\'h1000000 - {1\'b0, r_t2};')
        self.instruction('wire [23:0] w_e1 = w_e1_full[23:0];')
        self.instruction('wire [23:0] w_e2 = w_e2_full[23:0];')
        self.instruction('')
        self.comment('Newton refine products: (r*e + 2^22) >> 23, saturated at 2^24-1')
        self.instruction("wire [47:0] w_re_sum = w_prod + 48'h000000400000;")
        self.instruction('wire [24:0] w_r1_wide = w_re_sum[47:23];')
        self.instruction('wire [24:0] w_r2_wide = w_re_sum[47:23];')
        self.instruction('')

    def generate_rne_logic(self):
        """Exact residual reduction, textbook RNE, and result assembly.

        All combinational, feeding the S_RNE output registers.
        """
        self.comment('-' * 73)
        self.comment('Exact residual rounding (S_RNE, combinational)')
        self.instruction('')
        self.comment('rem = B*(sig_true - q0) in [0, 16B) exactly. Reduce')
        self.comment('rem = k*B + remp with a 4-stage binary chain (8B, 4B, 2B, B),')
        self.comment('then q_base = q0 + k and textbook RNE on the exact remainder:')
        self.comment('  round up iff (2*remp > B) | ((2*remp == B) & LSB(q_base))')
        self.comment('TRUE sticky by construction: the residual is exact, so a tie')
        self.comment('(2*remp == B) is detected exactly and rounds to even.')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction('logic [3:0]  w_k;')
        self.instruction('logic [27:0] w_red;')
        self.comment('  every stage explicitly 28 bits wide')
        self.instruction("wire [27:0] w_b8 = {1'b0, r_b24, 3'b000};")
        self.instruction("wire [27:0] w_b4 = {2'b00, r_b24, 2'b00};")
        self.instruction("wire [27:0] w_b2 = {3'b000, r_b24, 1'b0};")
        self.instruction("wire [27:0] w_b1 = {4'b0000, r_b24};")
        self.instruction('always_comb begin')
        self.instruction("    w_k  = 4'd0;")
        self.instruction('    w_red = r_rem;')
        self.instruction('    if (w_red >= w_b8) begin')
        self.instruction('        w_red = w_red - w_b8;')
        self.instruction("        w_k = 4'd8;")
        self.instruction('    end')
        self.instruction('    if (w_red >= w_b4) begin')
        self.instruction('        w_red = w_red - w_b4;')
        self.instruction("        w_k = w_k + 4'd4;")
        self.instruction('    end')
        self.instruction('    if (w_red >= w_b2) begin')
        self.instruction('        w_red = w_red - w_b2;')
        self.instruction("        w_k = w_k + 4'd2;")
        self.instruction('    end')
        self.instruction('    if (w_red >= w_b1) begin')
        self.instruction('        w_red = w_red - w_b1;')
        self.instruction("        w_k = w_k + 4'd1;")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction("wire [24:0] w_qbase = {1'b0, r_q0} + {21'b0, w_k};")
        self.instruction("wire [24:0] w_two   = {w_red[23:0], 1'b0};  // 2*remp")
        self.comment('  remp < B < 2^24 so 2*remp fits 25 bits')
        self.instruction("wire w_ru = (w_two > {1'b0, r_b24}) |")
        self.instruction("          ((w_two == {1'b0, r_b24}) & w_qbase[0]);")
        self.instruction('wire [24:0] w_qf = w_qbase + {24\'b0, w_ru};')
        self.instruction("wire w_inexact = (w_red != 28'h0000000);")
        self.instruction('')
        self.comment('Quotient exponent: e_f = ea_s - eb_s + 127 - half')
        self.instruction("wire signed [10:0] w_e_f = $signed({r_ea_s[9], r_ea_s}) -")
        self.instruction("    $signed({r_eb_s[9], r_eb_s}) + 11'sd127 - {10'b0000000000, r_half};")
        self.instruction('')
        self.comment('Stage outputs (expression part-selects spelled out for tool')
        self.comment('compatibility): q0 with its 8-S-unit bias, exact residual')
        self.instruction('wire [47:0] w_bias = r_half ? 48\'h000004000000 : 48\'h000008000000;')
        self.instruction("wire [47:0] w_q0_full = (w_prod - w_bias) >> (5'd24 - {4'b0000, r_half});")
        self.instruction("wire [47:0] w_a_s = {1'b0, r_a24, 23'h0000000} << r_half;")
        self.instruction("wire [47:0] w_rem_full = w_a_s - w_prod;  // B*q0 < 2^48")
        self.instruction('')
        self.comment('Subnormal grid (SUBNORMAL_SUPPORT=1), EXACT like the normal path:')
        self.comment('the result grid (shift sh = 1-e_f) can be COARSER than the 24-bit')
        self.comment('significand grid, so re-rounding the rounded q_f would double-')
        self.comment('round. Instead the exact value q_base + red/B is compared at the')
        self.comment('result grid: with m = q_base mod 2^sh and X = m*B + red,')
        self.comment('  N_true = (q_base + red/B) / 2^sh, frac = X / (2^sh * B)')
        self.comment('  g = X >= B<<(sh-1); r = 2*rem_g >= B<<(sh-1);')
        self.comment('  sticky = remainder != 0; inexact = (X != 0)')
        self.comment('all exact integer compares (the m*B product is computed by the')
        self.comment('shared multiplier during S_RNE, one extra cycle for subnormal')
        self.comment('results). Deep shifts (sh >= 25) flush in S_RNE as before.')
        self.instruction("wire [7:0] w_sh = (w_e_f <= 11'sd0) ? (8'd1 - w_e_f[7:0]) : 8'd0;")
        self.instruction('wire        w_deep = (w_e_f < -11\'sd23);  // shift >= 25: guard bit gone')
        self.comment('  q_base WITHOUT the normal-path round-up: the exact integer part')
        self.instruction('wire [24:0] w_qbase_x = {1\'b0, r_q0} + {21\'b0, w_k};')
        self.instruction("assign w_m = w_qbase_x[23:0] & ((24'h000001 << w_sh[4:0]) - 24'h000001);")
        self.instruction("wire        w_need_subn = (w_e_f <= 11'sd0) & SUBNORMAL_SUPPORT & ~w_deep;")
        self.instruction('')
        self.comment('S_SUBN: exact grid compares from the registered m*B product')
        self.instruction('wire [47:0] w_x_sub = r_mprod + {20\'h00000, r_red};')
        self.instruction("wire [47:0] w_bsh  = {24'h000000, r_b24} << (r_sh - 5'd1);")
        self.instruction('wire        w_g_sn = (w_x_sub >= w_bsh);')
        self.instruction("wire [47:0] w_rg_sn = w_x_sub - (w_g_sn ? w_bsh : 48'h000000000000);")
        self.instruction("wire [48:0] w_2rg   = {w_rg_sn, 1'b0};")
        self.instruction('wire        w_r_sn = (w_2rg >= {1\'b0, w_bsh});')
        self.instruction("wire [48:0] w_rr_sn = w_2rg - (w_r_sn ? {1'b0, w_bsh} : 49'h0000000000000);")
        self.instruction("wire        w_s_sn = (w_rr_sn != 49'h0000000000000);")
        self.instruction('wire        w_inex_sn = (w_x_sub != 48\'h000000000000);')
        self.instruction('wire [23:0] w_n_sn = r_qbase >> r_sh;')
        self.instruction('wire        w_ru_sn = w_g_sn & (w_r_sn | w_s_sn | w_n_sn[0]);')
        self.instruction("wire [23:0] w_n_rnd = w_n_sn + {23'b0, w_ru_sn};")
        self.instruction('wire        w_sub_carry = w_n_rnd[23];  // BUG-004: -> min-normal')
        self.instruction('')

    def generate_output_assembly(self):
        """Final output mux: special / normal / FTZ+deep flush (S_RNE) and
        the exact subnormal-grid result (S_SUBN)."""
        self.comment('-' * 73)
        self.comment('Result assembly (S_RNE, combinational into output regs).')
        self.comment('The subnormal GRID result is NOT assembled here: re-rounding')
        self.comment('q_f at a coarser grid would double-round, so grid-bound')
        self.comment('results complete one cycle later in S_SUBN from the exact')
        self.comment('X = m*B + red comparison.')
        self.comment('-' * 73)
        self.comment('Stage-output declarations precede every use (lint clean).')
        self.instruction('logic [31:0] w_out_result;')
        self.instruction('logic w_out_overflow, w_out_underflow, w_out_invalid;')
        self.instruction('logic [31:0] w_subn_result;')
        self.instruction('logic w_subn_underflow;')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    w_out_result  = {r_sign, 8\'h00, 23\'h000000};')
        self.instruction("    w_out_overflow  = 1'b0;")
        self.instruction("    w_out_underflow = 1'b0;")
        self.instruction("    w_out_invalid   = 1'b0;")
        self.instruction("    if (w_e_f >= 11'sd255) begin")
        self.comment('        // Overflow: quotient magnitude >= 2^128')
        self.instruction("        w_out_result  = {r_sign, 8'hFF, 23'h000000};")
        self.instruction("        w_out_overflow = 1'b1;")
        self.instruction("    end else if (w_e_f >= 11'sd1) begin")
        self.comment('        // Normal range')
        self.instruction('        w_out_result  = {r_sign, w_e_f[7:0], w_qf[22:0]};')
        self.instruction("    end else if (!SUBNORMAL_SUPPORT) begin")
        self.comment('        // FTZ: nonzero quotient flushes to signed zero + flag')
        self.instruction("        w_out_underflow = 1'b1;")
        self.instruction('    end else begin')
        self.comment('        // deep shift (>= 25): below half min_sub, signed zero + flag')
        self.instruction("        w_out_underflow = 1'b1;")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.comment('S_SUBN output: exact subnormal-grid result')
        self.instruction('always_comb begin')
        self.instruction('    w_subn_result  = {r_sign, 8\'h00, w_n_rnd[22:0]};')
        self.instruction("    w_subn_underflow = 1'b0;")
        self.instruction("    if (w_sub_carry) begin")
        self.comment('        // BUG-004: rounding carry out of pre-round exponent 0')
        self.comment('        // yields min-normal, not a flush; not tiny, no flag')
        self.instruction("        w_subn_result  = {r_sign, 8'h01, 23'h000000};")
        self.instruction('    end else begin')
        self.comment('        // IEEE underflow: tiny after rounding AND inexact')
        self.instruction('        w_subn_underflow = w_inex_sn;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def generate_fsm(self):
        """The multi-cycle control FSM and output registers."""
        self.comment('-' * 73)
        self.comment('Multi-cycle FSM: 9 cycles accept-to-ow_valid on the normal')
        self.comment('path (10 for exact subnormal-grid results, which need the')
        self.comment('m*B compare cycle), 1 cycle for special cases. ow_valid')
        self.comment('pulses for exactly one cycle.')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction('assign ow_result  = r_result;')
        self.instruction('assign ow_overflow  = r_overflow;')
        self.instruction('assign ow_underflow = r_underflow;')
        self.instruction('assign ow_invalid   = r_invalid;')
        self.instruction('assign ow_valid     = r_owv;')
        self.instruction('')
        self.instruction('always_ff @(posedge i_clk or negedge i_rst_n) begin')
        self.instruction('    if (!i_rst_n) begin')
        self.instruction("        r_state    <= S_IDLE;")
        self.instruction("        r_owv      <= 1'b0;")
        self.instruction("        r_result   <= 32'h00000000;")
        self.instruction("        r_overflow <= 1'b0;")
        self.instruction("        r_underflow <= 1'b0;")
        self.instruction("        r_invalid  <= 1'b0;")
        self.instruction("        r_a24      <= 24'h000000;")
        self.instruction("        r_b24      <= 24'h000000;")
        self.instruction("        r_ea_s     <= 10'sd0;")
        self.instruction("        r_eb_s     <= 10'sd0;")
        self.instruction("        r_sign     <= 1'b0;")
        self.instruction("        r_half     <= 1'b0;")
        self.instruction("        r_r0       <= 24'h000000;")
        self.instruction("        r_t1       <= 24'h000000;")
        self.instruction("        r_r1       <= 24'h000000;")
        self.instruction("        r_t2       <= 24'h000000;")
        self.instruction("        r_r2       <= 24'h000000;")
        self.instruction("        r_q0       <= 24'h000000;")
        self.instruction("        r_rem      <= 28'h0000000;")
        self.instruction("        r_mprod    <= 48'h000000000000;")
        self.instruction("        r_red      <= 28'h0000000;")
        self.instruction("        r_qbase    <= 24'h000000;")
        self.instruction("        r_sh       <= 5'd0;")
        self.instruction('    end else begin')
        self.instruction("        r_owv <= 1'b0;")
        self.instruction('        case (r_state)')
        self.instruction('            S_IDLE: begin')
        self.instruction('                if (i_valid) begin')
        self.instruction('                    if (w_is_special) begin')
        self.instruction('                        r_result   <= w_spec_result;')
        self.instruction('                        r_overflow <= 1\'b0;')
        self.instruction('                        r_underflow <= 1\'b0;')
        self.instruction('                        r_invalid  <= w_spec_invalid;')
        self.instruction("                        r_owv      <= 1'b1;")
        self.instruction("                        r_state    <= S_OUT;")
        self.instruction('                    end else begin')
        self.instruction('                        r_a24   <= w_sig_a;')
        self.instruction('                        r_b24   <= w_sig_b;')
        self.instruction('                        r_ea_s  <= w_ea_s;')
        self.instruction('                        r_eb_s  <= w_eb_s;')
        self.instruction('                        r_sign  <= w_sign_result;')
        self.instruction('                        r_half  <= w_half;')
        self.instruction("                        r_state <= S_LUT;")
        self.instruction('                    end')
        self.instruction('                end')
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_LUT: begin')
        self.instruction("                r_r0   <= {r_lut_val, 12'h000};")
        self.instruction("                r_state <= S_NR1A;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_NR1A: begin')
        self.instruction('                r_t1    <= w_prod[47:24];  // t1 = trunc(B*r0 * 2^-24) * 2^23')
        self.instruction("                r_state <= S_NR1B;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_NR1B: begin')
        self.comment('                // r1 = round(r0*(2-t1)); saturate at 2^24-1')
        self.instruction('                r_r1    <= w_r1_wide[24] ? 24\'hFFFFFF : w_r1_wide[23:0];')
        self.instruction("                r_state <= S_NR2A;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_NR2A: begin')
        self.instruction('                r_t2    <= w_prod[47:24];')
        self.instruction("                r_state <= S_NR2B;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_NR2B: begin')
        self.instruction('                r_r2    <= w_r2_wide[24] ? 24\'hFFFFFF : w_r2_wide[23:0];')
        self.instruction("                r_state <= S_Q0;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_Q0: begin')
        self.comment('                // q0 = (A*r2 - bias) >> (24-half); the 8-S-unit bias')
        self.comment('                // (8<<23 when half, 8<<24 otherwise) keeps the exact')
        self.comment('                // residual non-negative')
        self.instruction('                r_q0    <= w_q0_full[23:0];')
        self.instruction("                r_state <= S_REM;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_REM: begin')
        self.comment('                // rem = (A << (23+half)) - B*q0, exact, in [0, 16B)')
        self.instruction('                r_rem   <= w_rem_full[27:0];')
        self.instruction("                r_state <= S_RNE;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_RNE: begin')
        self.instruction('                if (w_need_subn) begin')
        self.comment('                    // subnormal grid: carry the EXACT value into')
        self.comment('                    // S_SUBN (m*B from the multiplier this cycle)')
        self.instruction('                    r_mprod    <= w_prod;')
        self.instruction('                    r_red      <= w_red;')
        self.instruction('                    r_qbase    <= w_qbase_x[23:0];')
        self.instruction('                    r_sh       <= w_sh[4:0];')
        self.instruction("                    r_state    <= S_SUBN;")
        self.instruction('                end else begin')
        self.instruction('                    r_result   <= w_out_result;')
        self.instruction('                    r_overflow <= w_out_overflow;')
        self.instruction('                    r_underflow <= w_out_underflow;')
        self.instruction('                    r_invalid  <= w_out_invalid;')
        self.instruction("                    r_owv      <= 1'b1;")
        self.instruction("                    r_state    <= S_OUT;")
        self.instruction('                end')
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_SUBN: begin')
        self.comment('                // exact subnormal-grid result (RNE, TRUE sticky)')
        self.instruction('                r_result   <= w_subn_result;')
        self.instruction("                r_overflow <= 1'b0;")
        self.instruction('                r_underflow <= w_subn_underflow;')
        self.instruction("                r_invalid  <= 1'b0;")
        self.instruction("                r_owv      <= 1'b1;")
        self.instruction("                r_state    <= S_OUT;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_OUT: begin')
        self.instruction("                r_state <= S_IDLE;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            default: begin')
        self.instruction("                r_state <= S_IDLE;")
        self.instruction('            end')
        self.instruction('        endcase')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 divider."""
        # Generate-time proof obligations: the exactness preconditions.
        seed_worst, r2_worst = verify_accuracy_bounds()
        seed_rel = 47 - seed_worst.bit_length() + 1
        r2_rel = 47 - r2_worst.bit_length() + 1
        print(f'  fp32_divider: seed |r0*b-1| <= 2^-{seed_rel}, '
              f'Newton |B*r2-2^47| <= {r2_worst} (2^-{r2_rel}) over all 2^24 divisors')

        self.generate_fsm_states()
        self.generate_input_decode()
        self.generate_special_case_logic()
        self.generate_operand_preparation()
        # Datapath registers precede the LUT: w_lut_idx reads r_state/r_b24
        self.generate_datapath_registers()
        self.generate_reciprocal_lut()
        self.generate_multiply_unit()
        self.generate_rne_logic()
        self.generate_output_assembly()
        self.generate_fsm()

        self.start()
        self.generate_parameter()
        self.end()

        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 divider (Goldschmidt-class multiplicative divide '
                    'with exact-residual RNE, 9-cycle iterative (10 for subnormal-grid) latency)',
            generator_script='fp32_divider.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_divider(output_path):
    """
    Generate complete FP32 divider.

    Args:
        output_path: Directory to write the generated file
    """
    divider = FP32Divider()
    divider.verilog(output_path)
    return divider.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_divider(output_path)
    print(f'Generated: {module_name}.sv')
