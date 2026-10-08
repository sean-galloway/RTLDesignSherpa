# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32Sqrt
# Purpose: Complete IEEE 754-2008 FP32 Square Root Generator
#
# Implements a latency-optimized IEEE 754-2008 single-precision square root:
#   sqrt(x) = b * r2 with r -> 1/sqrt(b) refined by Newton iteration, the
#   significand root biased down by a generate-time-measured constant so the
#   EXACT integer residual rem = W - y0^2 (W = S << (23+parity)) lands in the
#   4-bit reduction window, making the final rounding textbook RNE with TRUE
#   (unfolded) sticky -- not a bounded-ulp approximation.
#
# Algorithm (Newton-Raphson reciprocal-sqrt, latency-optimized):
#   1. Reciprocal-sqrt seed r0 from a 7-bit-index / 12-bit-entry LUT over the
#      significand top bits (bucket-center design, integer-exact):
#      entry = round(2^11 * sqrt(2/b_center)), targeting
#      r* = 2^23*sqrt(2/b) so every seed stays >= 2^23 (true hidden bit).
#      Measured |r0/r0* - 1| <= 2^-8 class at every bucket end (asserted).
#   2. Two textbook Newton refinements r' = r*(3/2 - b*r^2/2) on the shared
#      24x24 family significand multiplier, one multiply per FSM cycle:
#        u = (r*r) >> 23 ; t = (b*u + 2^24) >> 25 ; e = 3*2^22 - t ;
#        r' = (r*e + 2^22) >> 23  (saturated at 2^24-1)
#      u is r^2 at the 2^23 scale (24-bit operand, exhaustively proven < 2^24
#      for every reachable r), t is b*r^2 at the 2^23 scale so
#      e = (3/2 - b*r^2/2) * 2^23. The seed error squares twice: 2^-8 ->
#      2^-16 -> 2^-32, so after two refinements the residual error is pure
#      fixed-point rounding noise. Exhaustively verified over ALL 2^24
#      significands at generate time: the biased significand root y0
#      satisfies y0 <= Y_real and Y_real - y0 <= 10 (reduction window 15),
#      and the corrected result equals the exact integer oracle RNE(sqrt(W))
#      on every one of the 2^25 (S, parity) pairs.
#   3. y = b*r2 (~2^23*sqrt(2b), saturated), then odd/even exponent handling:
#      with the input value = S * 2^(E_x - 23), g = E_x mod 2 and
#      e_r = floor(E_x/2) + 127, the exact result significand is
#      Y_real = sqrt(S << (23+g)) in [2^23, 2^24). Odd E_x (g=1) uses y
#      directly (y ~ 2^23*sqrt(2b) = Y_real); even E_x (g=0) scales the
#      significand root by 1/sqrt(2) (one multiply by the
#      round(2^23/sqrt(2)) constant). y is then biased DOWN by BIAS = 8
#      (measured max y0raw - Y_real = 8 over the exhaustive sweep).
#   4. Exact residual rounding (S_RNE): rem = W - y0^2 in [0, 15*2y0). A
#      4-stage binary chain (8, 4, 2, 1) tests (y0+k+step)^2 <= W with
#      incremental squares -- exact integer compares -- so Y_base = y0 + k
#      with (Y_base+1)^2 > W. Round up iff rem' = W - Y_base^2 >= Y_base+1,
#      i.e. iff Y_real >= Y_base + 1/2. Half-ULP ties can NEVER occur (W is
#      an integer, (k+1/2)^2 = k^2+k+1/4 is not), so RNE degenerates to
#      exact round-to-nearest with TRUE sticky (inexact = rem' != 0). A
#      rounding carry out of the significand (y_f = 2^24) shifts to 2^23
#      and bumps the result exponent.
#   Latency: 10 cycles from the accept edge to ow_valid on the odd-exponent
#   path (11 counting the i_valid presentation cycle), 11 for even
#   exponents (12 with accept) which need the 1/sqrt(2) significand-scale
#   cycle, 1 cycle for special cases (2 with accept).
#
# FP32 Format (IEEE 754-2008):
#   [31]    - Sign bit
#   [30:23] - 8-bit biased exponent (bias = 127)
#   [22:0]  - 23-bit mantissa (implied leading 1 for normalized)
#
# Subnormal handling:
#   SUBNORMAL_SUPPORT=0 (default): FTZ. Subnormal inputs are treated as
#     +/-zero (result +/-0 with the input sign, no invalid, no underflow).
#     Results are never subnormal (see below).
#   SUBNORMAL_SUPPORT=1: subnormal inputs are left-normalized into [1,2)
#     with exponent bookkeeping (effective exponent E_x = k-149, k the
#     leading-bit position) and run the normal path.
#   NOTE: a square root can NEVER underflow or overflow for finite fp32
#     inputs -- sqrt halves the exponent, pushing every magnitude toward
#     1: sqrt(2^-149) ~ 2^-74.5 and sqrt(2^128) < 2^64, both deep inside
#     the normal range. Results are therefore always normal, ow_underflow
#     is tied low by design (port kept for family interface symmetry), and
#     no subnormal-grid result path exists.
#
# Special cases (IEEE 754-2008):
#   - NaN in: canonical qNaN out, ow_invalid set
#   - sqrt(-inf): canonical qNaN out, ow_invalid set
#   - sqrt(+inf): +inf
#   - sqrt(+/-0): +/-0 (sign preserved, exact)
#   - sqrt(-x), x nonzero: canonical qNaN out, ow_invalid set
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header

# Reciprocal-sqrt seed LUT: 7-bit index (significand S[22:16]), 12-bit
# bucket-center entries targeting r* = 2^23 * sqrt(2/b); entries stay in
# [2048, 2896], so R0 = entry<<12 stays in [2^23, 2^23*sqrt(2)] with the
# true hidden bit set.
LUT_INDEX_BITS = 7
LUT_DATA_BITS = 12

# round(2^23 / sqrt(2)): significand-domain constant for the even-exponent
# 1/sqrt(2) scale. NOTE: this is 0x5A827A < 2^23, so its OWN bit 23 is 0 --
# the shared multiplier port must present 1'b0 (a hardwired 1 would graft a
# phantom hidden bit onto the constant).
C_INV_SQRT2 = round((1 << 23) / 2 ** 0.5)

# Down-bias for the exact-residual scheme: measured max(y0raw - Y_real) = 8
# over ALL 2^24 significands (both parities) at generate time. With BIAS=8
# the biased root y0 satisfies y0 <= Y_real and Y_real - y0 <= 10, inside
# the 4-bit (k <= 15) reduction window.
BIAS = 8


def _isqrt(n):
    """Exact integer square root (Newton, no float)."""
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


def _round_ratio_sqrt(num, den):
    """round(sqrt(num/den)) computed with integer compares only."""
    lo = _isqrt(num // den)
    return min((lo, lo + 1), key=lambda c: abs(c * c * den - num))


def _build_reciprocal_sqrt_lut():
    """Exact-integer bucket-center reciprocal-sqrt seed LUT (same
    construction the module documents).

    entry = round(2^11 * sqrt(2/b_center)) with the bucket-center
    significand integer B_center = 2^23 + (2*idx+1) * 2^(23-1-LUT_BITS).
    entry^2 ~= 2^46/B_center, so the entry is round(sqrt(2^46/B_center))
    chosen between the bracketing isqrts by the exact |c^2*B - 2^46| test.
    """
    lut = []
    for idx in range(1 << LUT_INDEX_BITS):
        b_center = (1 << 23) + ((2 * idx + 1) << (22 - LUT_INDEX_BITS))
        lut.append(_round_ratio_sqrt(1 << 46, b_center))
    return lut


RECIPROCAL_SQRT_LUT = _build_reciprocal_sqrt_lut()


def _pipe_model(S, g):
    """Bit-faithful fixed-point model of the generated datapath.

    Mirrors every truncation, rounding, and saturation the RTL performs.
    Returns (y0, e1, e2, u1, u2, R1, R2) with y0 the BIASED significand root.
    """
    def sat(x):
        return (1 << 24) - 1 if x >= (1 << 24) else x

    idx = (S >> (23 - LUT_INDEX_BITS)) & ((1 << LUT_INDEX_BITS) - 1)
    R0 = RECIPROCAL_SQRT_LUT[idx] << 12
    u1 = (R0 * R0) >> 23
    t1 = (S * u1 + (1 << 24)) >> 25
    e1 = (3 << 22) - t1
    R1 = sat((R0 * e1 + (1 << 22)) >> 23)
    u2 = (R1 * R1) >> 23
    t2 = (S * u2 + (1 << 24)) >> 25
    e2 = (3 << 22) - t2
    R2 = sat((R1 * e2 + (1 << 22)) >> 23)
    yc = sat((S * R2 + (1 << 22)) >> 23)
    if g == 0:
        y0raw = (yc * C_INV_SQRT2 + (1 << 22)) >> 23
    else:
        y0raw = yc
    return y0raw - BIAS, e1, e2, u1, u2, R1, R2


def _rne_model(y0, S, g):
    """Bit-faithful model of the S_RNE exact reduction + RNE."""
    W = S << (23 + g)
    sq = y0 * y0
    rem = W - sq
    assert rem >= 0, (hex(S), g, y0)
    k = 0
    cur = y0
    cursq = sq
    for sv in (8, 4, 2, 1):
        ty = cur + sv
        tsq = cursq + 2 * sv * cur + sv * sv
        if tsq <= W:
            cur = ty
            cursq = tsq
            k += sv
    remp = W - cursq
    ru = 1 if remp >= cur + 1 else 0
    yf = cur + ru
    inex = 1 if remp != 0 else 0
    carry = 1 if yf >= (1 << 24) else 0
    if carry:
        yf >>= 1
    return yf, inex, carry


def _oracle(S, g):
    """Exact integer RNE(sqrt(S << (23+g))) -> (y, inexact, carry)."""
    W = S << (23 + g)
    y = _isqrt(W)
    rem = W - y * y
    if rem >= y + 1:
        y += 1
    inex = 1 if rem != 0 else 0
    carry = 0
    if y >= (1 << 24):
        y >>= 1
        carry = 1
    return y, inex, carry


def verify_accuracy_bounds():
    """Generate-time proof obligations for the exact-rounding scheme.

    Exhaustively verifies, over ALL 2^24 significands S and both exponent
    parities g (2^25 cases):
      - seed error stays in the documented 2^-8 class (bucket ends, exact
        integer cross-multiplied compares)
      - u/r intermediate widths stay inside the shared multiplier's 24-bit
        operand domain (u < 2^24, r < 2^24: no operand truncation is ever
        possible)
      - both Newton factors stay 24-bit non-negative (e < 2^24)
      - the biased root y0 never exceeds Y_real and never sits more than
        15 below it (the 4-bit reduction window), with margin
      - the full pipeline (Newton + bias + exact reduction + RNE) equals
        the exact integer oracle on every case
    Returns (seed_rel_exponent, max_gap).
    """
    # Seed class: |R0/R0* - 1| at every bucket end, exact integer compares.
    # R0* = 2^23*sqrt(2/b), b = S/2^23  <=>  R0^2*S vs 2^70.
    seed_worst_num, seed_worst_den = 0, 1
    for idx in range(1 << LUT_INDEX_BITS):
        base = (1 << 23) + idx * (1 << (23 - LUT_INDEX_BITS))
        for low in (0, 1, (1 << (23 - LUT_INDEX_BITS)) // 2,
                    (1 << (23 - LUT_INDEX_BITS)) - 1):
            S = base + low
            if S >= (1 << 24):
                continue
            R0 = RECIPROCAL_SQRT_LUT[idx] << 12
            num = abs(R0 * R0 * S - (1 << 70))
            den = 1 << 70
            if num * seed_worst_den > seed_worst_num * den:
                seed_worst_num, seed_worst_den = num, den

    max_gap = 0
    for S in range(1 << 23, 1 << 24):
        for g in (0, 1):
            y0, e1, e2, u1, u2, R1, R2 = _pipe_model(S, g)
            W = S << (23 + g)
            assert u1 < (1 << 24), f'u1 {u1:#x} >= 2^24 at S={S:#x}'
            assert u2 < (1 << 24), f'u2 {u2:#x} >= 2^24 at S={S:#x}'
            assert R1 < (1 << 24), f'R1 {R1:#x} >= 2^24 at S={S:#x}'
            assert R2 < (1 << 24), f'R2 {R2:#x} >= 2^24 at S={S:#x}'
            assert 0 <= e1 < (1 << 24), f'e1 {e1:#x} out of range at S={S:#x}'
            assert 0 <= e2 < (1 << 24), f'e2 {e2:#x} out of range at S={S:#x}'
            assert y0 * y0 <= W, f'biased root above Y_real at S={S:#x} g={g}'
            r = _isqrt(W)
            gap = r - y0
            assert gap <= 15, f'Y_real - y0 = {gap} > 15 at S={S:#x} g={g}'
            if gap > max_gap:
                max_gap = gap
            assert _rne_model(y0, S, g) == _oracle(S, g), \
                f'pipeline != oracle at S={S:#x} g={g}'
    # The seed stays in the 2^-8 class (assert with slack over the measured
    # worst case).
    assert seed_worst_num * (1 << 7) < seed_worst_den, \
        f'seed error {seed_worst_num}/{seed_worst_den} out of 2^-7 class'
    seed_rel = 0
    while (1 << seed_rel) * seed_worst_num < seed_worst_den:
        seed_rel += 1
    return seed_rel - 1, max_gap


class FP32Sqrt(Module):
    """
    Generates the complete IEEE 754-2008 FP32 square root.

    Architecture (multi-cycle FSM, one 24x24 significand multiply per cycle):
    1. Accept: classify the operand, capture the normalized significand,
       exponent parity and halved result exponent, route special cases
       straight to the output register, seed r0 from the LUT.
    2. S_U1/S_T1/S_E1R: Newton refine #1 (u = r*r, t = b*u, r1 = r0*e1).
    3. S_U2/S_T2/S_E2R: Newton refine #2 (exhaustively bounded at generate
       time over all 2^24 significands).
    4. S_Y:     y = b*r2 (~2^23*sqrt(2b)).
    5. S_SCALE: even exponents (g=0): y *= 1/sqrt(2) (skipped for g=1).
    6. S_SQ:    exact square of the biased root y0.
    7. S_RNE:   exact 4-bit square-test reduction + textbook RNE with TRUE
       sticky; result assembly. ow_valid pulses one cycle.
    """

    module_str = 'math_ieee754_2008_fp32_sqrt'
    port_str = '''
    input  logic        i_clk,          // System clock
    input  logic        i_rst_n,        // Active-low async reset
    input  logic [31:0] i_a,            // FP32 radicand
    input  logic        i_valid,        // Input valid (single cycle)
    output logic [31:0] ow_result,      // FP32 square root
    output logic        ow_underflow,   // Tied low: sqrt never underflows (see header)
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
        self.instruction("                       S_U1    = 4'd1,")
        self.instruction("                       S_T1    = 4'd2,")
        self.instruction("                       S_E1R   = 4'd3,")
        self.instruction("                       S_U2    = 4'd4,")
        self.instruction("                       S_T2    = 4'd5,")
        self.instruction("                       S_E2R   = 4'd6,")
        self.instruction("                       S_Y     = 4'd7,")
        self.instruction("                       S_SCALE = 4'd8,")
        self.instruction("                       S_SQ    = 4'd9,")
        self.instruction("                       S_RNE   = 4'd10,")
        self.instruction("                       S_OUT   = 4'd11;")
        self.instruction('')

    def generate_input_decode(self):
        """Combinatorial operand decode straight from the inputs."""
        self.comment('Input field extraction (combinatorial, sampled at accept)')
        self.comment('Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa')
        self.instruction('')
        self.instruction('wire        w_sign_a = i_a[31];')
        self.instruction('wire [7:0]  w_exp_a  = i_a[30:23];')
        self.instruction('wire [22:0] w_mant_a = i_a[22:0];')
        self.instruction('')
        self.comment('Special value detection')
        self.instruction('')
        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);")
        self.instruction('')
        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);")
        self.instruction('')
        self.comment('Infinity: exp=FF, mant=0')
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);")
        self.instruction('')
        self.comment('NaN: exp=FF, mant!=0')
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);")
        self.instruction('')
        self.comment('Effective zero: FTZ folds subnormals into zero')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('')

    def generate_special_case_logic(self):
        """Special-case classification and result values (sampled at accept)."""
        self.comment('IEEE 754-2008 special cases (priority order)')
        self.comment('NaN in -> canonical qNaN + invalid; sqrt(-inf) -> qNaN + invalid;')
        self.comment('sqrt(+inf) -> +inf; sqrt(+/-0) -> +/-0 (sign kept);')
        self.comment('sqrt(-x) for nonzero x -> qNaN + invalid;')
        self.comment('FTZ: positive subnormal input acts as +0 (no invalid).')
        self.comment('Declared here (before first use); assigned in the mux below')
        self.instruction('reg [31:0] w_spec_result;')
        self.instruction('reg        w_spec_invalid;')
        self.instruction('')
        self.comment('Datapath runs only for positive, non-special operands')
        self.instruction('wire w_is_special = w_a_is_nan | w_a_is_inf | w_a_eff_zero | w_sign_a;')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    w_spec_result  = {w_sign_a, 8\'h00, 23\'h000000};')
        self.instruction('    w_spec_invalid = 1\'b0;')
        self.instruction("    if (w_a_is_nan | (w_a_is_inf & w_sign_a) |")
        self.instruction('        (~w_a_is_inf & ~w_a_eff_zero & w_sign_a)) begin')
        self.instruction('        w_spec_result  = {w_sign_a, 8\'hFF, 23\'h400000};')
        self.instruction("        w_spec_invalid = 1'b1;")
        self.instruction('    end else if (w_a_is_inf) begin')
        self.instruction("        w_spec_result = 32'h7F800000;")
        self.instruction('    end')
        self.comment('    remaining cases: +/-0 and FTZ subnormal -> signed zero by default')
        self.instruction('end')
        self.instruction('')

    def generate_operand_preparation(self):
        """Normalized significand, exponent parity, halved result exponent.

        The input value is S * 2^(E_x - 23) with S in [2^23, 2^24). With
        g = E_x mod 2 (two's-complement LSB == floor-mod-2 parity) and
        e_r = floor(E_x/2) + 127 (arithmetic shift), the exact result
        significand is Y_real = sqrt(S << (23+g)) in [2^23, 2^24).
        Subnormal operands (SUBNORMAL_SUPPORT=1) left-normalize with
        E_x = k-149, k the leading-bit position.
        """
        self.comment('-' * 73)
        self.comment('Operand preparation: 24-bit significand, exponent parity,')
        self.comment('halved result exponent. At SUBNORMAL_SUPPORT=1 a subnormal')
        self.comment('operand left-normalizes into [1,2) with E_x = k-149; at =0')
        self.comment('subnormals never reach this path (effective zero routed to')
        self.comment('the special cases).')
        self.comment('-' * 73)
        self.instruction('')
        self.comment('Left-shift amount for a subnormal operand: 23 - leading-bit-pos,')
        self.comment('last assignment wins (loop keeps the highest set bit)')
        self.instruction('logic [4:0] r_a_sub_shift;')
        self.instruction('always_comb begin')
        self.instruction("    r_a_sub_shift = 5'd0;")
        self.instruction('    for (int i = 0; i < 23; i++) begin')
        self.instruction("        if (w_mant_a[i]) r_a_sub_shift = 5'd23 - 5'(i);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.comment('Significand with hidden bit: subnormal operand = {1\'b0, mant} << shift')
        self.instruction('wire [23:0] w_sig_a_norm = {1\'b0, w_mant_a} << r_a_sub_shift;')
        self.instruction("wire [23:0] w_sig_a = SUBNORMAL_SUPPORT & w_a_is_subnormal ?")
        self.instruction("    w_sig_a_norm : {1'b1, w_mant_a};")
        self.instruction('')
        self.comment('Effective exponent E_x (signed): subnormal operates at k-149')
        self.instruction("wire signed [10:0] w_ex_sub = -11'sd126 - $signed({6'b000000, r_a_sub_shift});")
        self.instruction("wire signed [10:0] w_ex_s = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ?")
        self.instruction("    w_ex_sub : ($signed({3'b000, w_exp_a}) - 11'sd127);")
        self.instruction('')
        self.comment('Exponent parity (two\'s-complement LSB == floor-mod-2) and the')
        self.comment('halved biased result exponent e_r = floor(E_x/2) + 127')
        self.instruction('wire w_g = w_ex_s[0];')
        self.instruction("wire signed [10:0] w_er_s = (w_ex_s >>> 1) + 11'sd127;")
        self.instruction('')

    def generate_reciprocal_sqrt_lut(self):
        """Emit the 128-entry reciprocal-sqrt seed LUT as a case statement."""
        self.comment('-' * 73)
        self.comment(f'Reciprocal-sqrt seed LUT: {LUT_INDEX_BITS}-bit index (significand')
        self.comment(f'S[22:16]), {LUT_DATA_BITS}-bit bucket-center entries targeting')
        self.comment('r* = 2^23*sqrt(2/b) so every seed keeps its true hidden bit.')
        self.comment('Measured |r0/r0* - 1| <= 2^-8 class at every bucket end; two')
        self.comment('Newton refinements follow (exhaustively bounded at generate')
        self.comment('time over all 2^24 significands).')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction(f'logic [{LUT_DATA_BITS-1}:0] r_lut_val;')
        self.comment('Index mux: operand is live at accept, registered afterwards')
        self.instruction(f'wire [{LUT_INDEX_BITS-1}:0] w_lut_idx =')
        self.instruction("    (r_state == S_IDLE) ? w_sig_a[22:16] : r_s24[22:16];")
        self.instruction('always_comb begin')
        self.instruction('    case (w_lut_idx)')
        for idx, entry in enumerate(RECIPROCAL_SQRT_LUT):
            self.instruction(f"        {LUT_INDEX_BITS}'d{idx}: r_lut_val = "
                             f"{LUT_DATA_BITS}'h{entry:03X};")
        self.instruction("        default: r_lut_val = 12'h000;")
        self.instruction('    endcase')
        self.instruction('end')
        self.instruction('')

    def generate_datapath_registers(self):
        """Datapath registers and the Newton-stage wiring."""
        self.comment('Registered operands and datapath state')
        self.instruction('logic [3:0]   r_state;')
        self.instruction('logic [23:0]  r_s24;')
        self.instruction('logic         r_g;')
        self.instruction('logic [8:0]   r_er;')
        self.instruction('logic [23:0]  r_r0, r_u1, r_t1, r_r1, r_u2, r_t2, r_r2;')
        self.instruction('logic [23:0]  r_yc, r_y0;')
        self.instruction('logic [47:0]  r_sq;     // S_SQ: exact biased-root square')
        self.instruction('logic [31:0]  r_result;')
        self.instruction('logic         r_underflow, r_invalid, r_owv;')
        self.instruction('')
        self.comment('Newton factor: e = 3/2 - b*r^2/2 at the 2^23 scale')
        self.comment('(t = b*r^2 at 2^23; exhaustively verified: e stays in')
        self.comment('[2^23/2, 2^24) so its own bit 23 is the true hidden bit on')
        self.comment('the multiplier B port)')
        self.instruction("wire [24:0] w_e1_full = 25'h0C00000 - {1'b0, r_t1};")
        self.instruction("wire [24:0] w_e2_full = 25'h0C00000 - {1'b0, r_t2};")
        self.instruction('wire [23:0] w_e1 = w_e1_full[23:0];')
        self.instruction('wire [23:0] w_e2 = w_e2_full[23:0];')
        self.instruction('')
        self.comment('Shared product tail: refine products (r*e, b*r2) and the')
        self.comment('1/sqrt(2) scale all add 2^22 then drop 23 bits; saturated')
        self.instruction("wire [48:0] w_ref_sum  = {1'b0, w_prod} + 49'h00000400000;")
        self.instruction('wire [25:0] w_ref_wide = w_ref_sum[48:23];')
        self.instruction("wire [23:0] w_ref_sat  = w_ref_wide[24] ? 24'hFFFFFF :")
        self.instruction('                                         w_ref_wide[23:0];')
        self.instruction("wire [23:0] w_ref_usat = w_ref_wide[23:0];")
        self.instruction('')
        self.comment('t-stage rounding: t = (b*u + 2^24) >> 25')
        self.instruction("wire [48:0] w_t_sum = {1'b0, w_prod} + 49'h000001000000;")

    def generate_multiply_unit(self):
        """The single shared 24x24 significand multiplier (one use per cycle)."""
        self.comment('-' * 73)
        self.comment('Shared significand multiplier: one 24x24 Dadda multiply per')
        self.comment('FSM cycle (Newton u/t/refine stages, the final y = b*r2, the')
        self.comment('1/sqrt(2) even-exponent scale, and the exact residual square')
        self.comment('all reuse this instance). i_*_is_normal IS the operand hidden')
        self.comment('bit, so each operand presents its own bit 23 in EVERY state:')
        self.comment('the 1/sqrt(2) constant is 0x5A827A < 2^23 (own bit 23 = 0),')
        self.comment('and the biased root y0 can sit at or below 2^23 (own bit 23')
        self.comment('may be 0). A hardwired 1 would graft a phantom hidden bit and')
        self.comment('corrupt the exact residual -- the divider slice\'s root-cause')
        self.comment('lesson. The exhaustive proof in verify_accuracy_bounds')
        self.comment('assumes exactly this reconstruction (plain 24x24 products).')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction('logic [22:0] w_mult_a;')
        self.instruction('logic [22:0] w_mult_b;')
        self.instruction('wire [47:0] w_prod;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp32_mantissa_mult u_mant_mult (')
        self.instruction('    .i_mant_a(w_mult_a),')
        self.instruction('    .i_mant_b(w_mult_b),')
        self.comment('    hidden-bit semantics per operand: i_*_is_normal IS the')
        self.comment('    operand hidden bit, so EVERY state presents its own bit 23')
        self.instruction("    .i_a_is_normal((r_state == S_SCALE) ? r_yc[23]   :")
        self.instruction("                   (r_state == S_SQ)    ? r_y0[23]   :")
        self.instruction("                   (r_state == S_T1)    ? r_s24[23]  :")
        self.instruction("                   (r_state == S_T2)    ? r_s24[23]  :")
        self.instruction("                   (r_state == S_Y)     ? r_s24[23]  :")
        self.instruction("                   (r_state == S_E1R)   ? r_r0[23]   :")
        self.instruction("                   (r_state == S_E2R)   ? r_r1[23]   :")
        self.instruction("                   (r_state == S_U1)    ? r_r0[23]   :")
        self.instruction("                   (r_state == S_U2)    ? r_r1[23]   : 1'b1),")
        self.comment('    S_SCALE B port: the 1/sqrt(2) constant\'s OWN bit 23 (=0)')
        self.instruction("    .i_b_is_normal((r_state == S_SCALE) ? 1'b0       :")
        self.instruction("                   (r_state == S_SQ)    ? r_y0[23]   :")
        self.instruction("                   (r_state == S_T1)    ? r_u1[23]   :")
        self.instruction("                   (r_state == S_T2)    ? r_u2[23]   :")
        self.instruction("                   (r_state == S_Y)     ? r_r2[23]   :")
        self.instruction("                   (r_state == S_E1R)   ? w_e1[23]   :")
        self.instruction("                   (r_state == S_E2R)   ? w_e2[23]   :")
        self.instruction("                   (r_state == S_U1)    ? r_r0[23]   :")
        self.instruction("                   (r_state == S_U2)    ? r_r1[23]   : 1'b1),")
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
        self.instruction('        S_U1: begin')
        self.instruction('            w_mult_a = r_r0[22:0];')
        self.instruction('            w_mult_b = r_r0[22:0];')
        self.instruction('        end')
        self.instruction('        S_T1: begin')
        self.instruction('            w_mult_a = r_s24[22:0];')
        self.instruction('            w_mult_b = r_u1[22:0];')
        self.instruction('        end')
        self.instruction('        S_E1R: begin')
        self.instruction('            w_mult_a = r_r0[22:0];')
        self.instruction('            w_mult_b = w_e1[22:0];')
        self.instruction('        end')
        self.instruction('        S_U2: begin')
        self.instruction('            w_mult_a = r_r1[22:0];')
        self.instruction('            w_mult_b = r_r1[22:0];')
        self.instruction('        end')
        self.instruction('        S_T2: begin')
        self.instruction('            w_mult_a = r_s24[22:0];')
        self.instruction('            w_mult_b = r_u2[22:0];')
        self.instruction('        end')
        self.instruction('        S_E2R: begin')
        self.instruction('            w_mult_a = r_r1[22:0];')
        self.instruction('            w_mult_b = w_e2[22:0];')
        self.instruction('        end')
        self.instruction('        S_Y: begin')
        self.instruction('            w_mult_a = r_s24[22:0];')
        self.instruction('            w_mult_b = r_r2[22:0];')
        self.instruction('        end')
        self.instruction("        S_SCALE: begin")
        self.comment('            even exponents: scale the significand root by')
        self.comment('            1/sqrt(2) = 0x5A827A (own bit 23 = 0, see above)')
        self.instruction('            w_mult_a = r_yc[22:0];')
        self.instruction("            w_mult_b = 23'h5A827A;")
        self.instruction('        end')
        self.instruction('        S_SQ: begin')
        self.comment('            exact residual: square of the biased root')
        self.instruction('            w_mult_a = r_y0[22:0];')
        self.instruction('            w_mult_b = r_y0[22:0];')
        self.instruction('        end')
        self.instruction('        default: begin')
        self.instruction("            w_mult_a = 23'h000000;")
        self.instruction("            w_mult_b = 23'h000000;")
        self.instruction('        end')
        self.instruction('    endcase')
        self.instruction('end')
        self.instruction('')

    def generate_rne_logic(self):
        """Exact residual reduction, textbook RNE, and result assembly."""
        self.comment('-' * 73)
        self.comment('Exact residual rounding (S_RNE, combinational)')
        self.instruction('')
        self.comment('rem = W - y0^2 in [0, 15*2y0) exactly (W = S<<(23+g) is the')
        self.comment('exact radicand). A 4-stage binary chain (8, 4, 2, 1) tests')
        self.comment('(y0+k+step)^2 <= W with incremental squares -- exact integer')
        self.comment('compares -- so Y_base = y0+k with (Y_base+1)^2 > W. Round up')
        self.comment("iff rem' = W - Y_base^2 >= Y_base+1, i.e. Y_real >= Y_base+1/2.")
        self.comment('Half-ULP ties can NEVER occur (W is an integer, (k+1/2)^2 is')
        self.comment("not), so RNE degenerates to exact round-to-nearest with TRUE")
        self.comment("sticky (inexact = rem' != 0). No unfaithful last bit.")
        self.comment('-' * 73)
        self.instruction('')
        self.comment('Exact radicand W = S << (23+g): 48 bits either parity')
        self.instruction("wire [47:0] w_wp = r_g ? {r_s24, 24'h000000} :")
        self.instruction("                        {1'b0, r_s24, 23'h000000};")
        self.instruction("wire [48:0] w_rem = {1'b0, w_wp} - {1'b0, r_sq};  // >= 0 by proof")
        self.instruction('')
        self.comment('4-stage binary square-test chain (every stage explicit)')
        self.instruction('logic [24:0] w_kc;    // running y0+k')
        self.instruction('logic [48:0] w_ksq;   // running (y0+k)^2')
        self.instruction('always_comb begin')
        self.instruction("    w_kc  = {1'b0, r_y0};")
        self.instruction("    w_ksq = {1'b0, r_sq};")
        self.comment('    step 8: (cur+8)^2 = cursq + (cur<<4) + 64')
        self.instruction("    if ((w_ksq + {20'b00000000000000000000, w_kc, 4'b0000} + 49'd64) <= {1'b0, w_wp}) begin")
        self.instruction("        w_ksq = w_ksq + {20'b00000000000000000000, w_kc, 4'b0000} + 49'd64;")
        self.instruction("        w_kc = w_kc + 25'd8;")
        self.instruction('    end')
        self.comment('    step 4: (cur+4)^2 = cursq + (cur<<3) + 16')
        self.instruction("    if ((w_ksq + {21'b000000000000000000000, w_kc, 3'b000} + 49'd16) <= {1'b0, w_wp}) begin")
        self.instruction("        w_ksq = w_ksq + {21'b000000000000000000000, w_kc, 3'b000} + 49'd16;")
        self.instruction("        w_kc = w_kc + 25'd4;")
        self.instruction('    end')
        self.comment('    step 2: (cur+2)^2 = cursq + (cur<<2) + 4')
        self.instruction("    if ((w_ksq + {22'b0000000000000000000000, w_kc, 2'b00} + 49'd4) <= {1'b0, w_wp}) begin")
        self.instruction("        w_ksq = w_ksq + {22'b0000000000000000000000, w_kc, 2'b00} + 49'd4;")
        self.instruction("        w_kc = w_kc + 25'd2;")
        self.instruction('    end')
        self.comment('    step 1: (cur+1)^2 = cursq + (cur<<1) + 1')
        self.instruction("    if ((w_ksq + {23'b00000000000000000000000, w_kc, 1'b0} + 49'd1) <= {1'b0, w_wp}) begin")
        self.instruction("        w_ksq = w_ksq + {23'b00000000000000000000000, w_kc, 1'b0} + 49'd1;")
        self.instruction("        w_kc = w_kc + 25'd1;")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction("wire [48:0] w_remp  = {1'b0, w_wp} - w_ksq;        // in [0, 2*Y_base]")
        self.instruction("wire        w_ru    = (w_remp >= {24'b000000000000000000000000, w_kc} + 49'd1);")
        self.instruction("wire [25:0] w_yf    = {1'b0, w_kc} + {25'b0000000000000000000000000, w_ru};")
        self.instruction('wire        w_carry = w_yf[24];                   // rounding carry out')
        self.instruction("wire [23:0] w_ysig  = w_carry ? 24'h800000 : w_yf[23:0];")
        self.instruction("wire        w_inexact = (w_remp != 49'd0);")
        self.instruction('')
        self.comment('Result exponent: e_r + carry (carry out of the significand)')
        self.instruction("wire [9:0] w_er_f = {1'b0, r_er} + {9'b000000000, w_carry};")
        self.instruction("wire [31:0] w_out_result = {1'b0, w_er_f[7:0], w_ysig[22:0]};")
        self.instruction('')

    def generate_fsm(self):
        """The multi-cycle control FSM and output registers."""
        self.comment('-' * 73)
        self.comment('Multi-cycle FSM: 10 cycles accept-to-ow_valid on the odd-')
        self.comment('exponent path (11 for even exponents, which need the')
        self.comment('1/sqrt(2) significand-scale cycle), 1 cycle for special')
        self.comment('cases. ow_valid pulses for exactly one cycle.')
        self.comment('-' * 73)
        self.instruction('')
        self.instruction('assign ow_result    = r_result;')
        self.instruction("assign ow_underflow = r_underflow;  // tied low: sqrt never underflows")
        self.instruction('assign ow_invalid   = r_invalid;')
        self.instruction('assign ow_valid     = r_owv;')
        self.instruction('')
        self.instruction('always_ff @(posedge i_clk or negedge i_rst_n) begin')
        self.instruction('    if (!i_rst_n) begin')
        self.instruction("        r_state     <= S_IDLE;")
        self.instruction("        r_owv       <= 1'b0;")
        self.instruction("        r_result    <= 32'h00000000;")
        self.instruction("        r_underflow <= 1'b0;")
        self.instruction("        r_invalid   <= 1'b0;")
        self.instruction("        r_s24       <= 24'h000000;")
        self.instruction("        r_g         <= 1'b0;")
        self.instruction("        r_er        <= 9'd0;")
        self.instruction("        r_r0        <= 24'h000000;")
        self.instruction("        r_u1        <= 24'h000000;")
        self.instruction("        r_t1        <= 24'h000000;")
        self.instruction("        r_r1        <= 24'h000000;")
        self.instruction("        r_u2        <= 24'h000000;")
        self.instruction("        r_t2        <= 24'h000000;")
        self.instruction("        r_r2        <= 24'h000000;")
        self.instruction("        r_yc        <= 24'h000000;")
        self.instruction("        r_y0        <= 24'h000000;")
        self.instruction("        r_sq        <= 48'h000000000000;")
        self.instruction('    end else begin')
        self.instruction("        r_owv <= 1'b0;")
        self.instruction('        case (r_state)')
        self.instruction('            S_IDLE: begin')
        self.instruction('                if (i_valid) begin')
        self.instruction('                    if (w_is_special) begin')
        self.instruction('                        r_result    <= w_spec_result;')
        self.instruction("                        r_underflow <= 1'b0;")
        self.instruction('                        r_invalid   <= w_spec_invalid;')
        self.instruction("                        r_owv       <= 1'b1;")
        self.instruction("                        r_state     <= S_OUT;")
        self.instruction('                    end else begin')
        self.instruction('                        r_s24 <= w_sig_a;')
        self.instruction('                        r_g   <= w_g;')
        self.instruction('                        r_er  <= w_er_s[8:0];')
        self.instruction("                        r_r0  <= {r_lut_val, 12'h000};")
        self.instruction("                        r_state <= S_U1;")
        self.instruction('                    end')
        self.instruction('                end')
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_U1: begin')
        self.comment('                // u1 = trunc(r0^2 * 2^-23), 24-bit operand')
        self.instruction('                r_u1    <= w_prod[46:23];')
        self.instruction("                r_state <= S_T1;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_T1: begin')
        self.comment('                // t1 = round(b*r0^2) at the 2^23 scale')
        self.instruction('                r_t1    <= w_t_sum[48:25];')
        self.instruction("                r_state <= S_E1R;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_E1R: begin')
        self.comment('                // r1 = round(r0*e1); saturate at 2^24-1')
        self.instruction('                r_r1    <= w_ref_sat;')
        self.instruction("                r_state <= S_U2;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_U2: begin')
        self.instruction('                r_u2    <= w_prod[46:23];')
        self.instruction("                r_state <= S_T2;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_T2: begin')
        self.instruction('                r_t2    <= w_t_sum[48:25];')
        self.instruction("                r_state <= S_E2R;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_E2R: begin')
        self.instruction('                r_r2    <= w_ref_sat;')
        self.instruction("                r_state <= S_Y;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_Y: begin')
        self.comment('                // yc = round(b*r2) ~ 2^23*sqrt(2b), saturated;')
        self.comment('                // odd exponents (g=1): y0 = yc - BIAS, scale skipped')
        self.instruction('                r_yc    <= w_ref_sat;')
        self.instruction('                if (r_g) begin')
        self.instruction('                    r_y0    <= w_ref_sat - 24\'d' + str(BIAS) + ';')
        self.instruction("                    r_state <= S_SQ;")
        self.instruction('                end else begin')
        self.instruction("                    r_state <= S_SCALE;")
        self.instruction('                end')
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_SCALE: begin')
        self.comment('                // even exponent: y0 = round(yc/sqrt(2)) - BIAS')
        self.instruction('                r_y0    <= w_ref_usat - 24\'d' + str(BIAS) + ';')
        self.instruction("                r_state <= S_SQ;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_SQ: begin')
        self.comment('                // exact square of the biased root for the residual')
        self.instruction('                r_sq    <= w_prod;')
        self.instruction("                r_state <= S_RNE;")
        self.instruction('            end')
        self.instruction('')
        self.instruction('            S_RNE: begin')
        self.instruction('                r_result    <= w_out_result;')
        self.instruction("                r_underflow <= 1'b0;  // tiny-after-rounding impossible")
        self.instruction("                r_invalid   <= 1'b0;")
        self.instruction("                r_owv       <= 1'b1;")
        self.instruction("                r_state     <= S_OUT;")
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
        """Generate the complete FP32 square root."""
        # Generate-time proof obligations: the exactness preconditions.
        seed_rel, max_gap = verify_accuracy_bounds()
        print(f'  fp32_sqrt: seed |r0/r0*-1| <= 2^-{seed_rel}, '
              f'Newton+reduction == exact oracle over all 2^24 significands '
              f'(both parities), max Y_real-y0 gap {max_gap}')

        self.generate_fsm_states()
        self.generate_input_decode()
        self.generate_special_case_logic()
        self.generate_operand_preparation()
        # Datapath registers precede the LUT: w_lut_idx reads r_state/r_s24
        self.generate_datapath_registers()
        self.generate_reciprocal_sqrt_lut()
        self.generate_multiply_unit()
        self.generate_rne_logic()
        self.generate_fsm()

        self.start()
        self.generate_parameter()
        self.end()

        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 square root (Newton-Raphson reciprocal-sqrt with exact-residual RNE, '
                    '10-cycle iterative (11 for even exponents) latency)',
            generator_script='fp32_sqrt.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_sqrt(output_path):
    """
    Generate complete FP32 square root.

    Args:
        output_path: Directory to write the generated file
    """
    sqrt = FP32Sqrt()
    sqrt.verilog(output_path)
    return sqrt.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_sqrt(output_path)
    print(f'Generated: {module_name}.sv')
