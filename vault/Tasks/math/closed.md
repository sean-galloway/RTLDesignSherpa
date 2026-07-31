<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Closed

_None._


---

## MATH-002 — bf16_adder underflow can report as +infinity/overflow (wrap bit shared by both flags)
**Status:** closed 2026-07-31 -- fix-RTL per Sean ("fix the math if they aren't to spec");
wrap-bit flag separation applied, directed FTZ regression added to
BF16AdderTB (underflow_ftz_test), mutation-checked (reverting the fix turns
3 cases RED).
**Priority:** P1 — possible RTL defect; doc promises FTZ-to-zero
**Owner:** Sean

`docs/markdown/rtl-math/math_bf16_adder.md` promises flush-to-zero:
"Output subnormals - Not generated (result goes to zero)", "FTZ mode",
"ow_underflow: 1 if result underflowed to zero". But in
`rtl/math/math_bf16_adder.sv`:

    wire w_exp_overflow  = w_exp_adjusted[8] || (w_exp_adjusted[7:0] >= 8'hFF);
    wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);

`w_exp_adjusted = {1'b0, r3_exp_l} - {5'b0, w_norm_shift_amt}` -- when the
normalization left shift exceeds exp_l the subtraction wraps negative and
bit 8 sets, asserting BOTH flags. The result-select chain tests the
overflow branch FIRST, so an underflowing result comes out as +infinity
with ow_overflow instead of zero with ow_underflow.

**Sim-settled 2026-07-31: the bug is REAL.** Directed case
(all PIPE_STAGEs=1): `0x0081 - 0x0080` (result ~2^-133, deep subnormal,
should FTZ to zero with ow_underflow) produces **0x7f80 (+inf), ow_overflow
= 1, ow_underflow = 0**; same for `0x0083 - 0x0080`. Sanity 1.0+1.0=2.0
passes. The wrap mechanism is confirmed: bit 8 of w_exp_adjusted is exactly
the negative sign of the exponent subtraction, so

    w_exp_overflow  = !w_exp_adjusted[8] && (w_exp_adjusted[7:0] >= 8'hFF);
    w_exp_underflow =  w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);

separates the flags (bit 8 cannot mean positive overflow here: shift is
bounded by the mantissa width, so a positive exp_l-shift never wraps).

**Remaining decision (Sean):** fix the RTL per the sketch above
(mutation-check with the same directed case), or declare inf-on-underflow
intended and rewrite the doc's FTZ promises. The doc currently reads as the
spec, and +inf on underflow is indefensible arithmetic -- the expected call
is fix-RTL, but it is your module.

