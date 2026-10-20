<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# The PWL LUT Activation

PRD roadmap item 2: a 256-entry lookup table with linear interpolation,
covering sigmoid, tanh, gelu, silu and exp with one row and bounded error.

## Segments

The segment index of a bf16 `x` is `{sign, octave[3:0], mant[6:4]}`, where
`octave = exp − 120`, clamped to [0, 15]. Segments are log-spaced: |x| in
[2^-7, 2^9) at eight segments per octave, both signs.

- |x| < 2^-7 uses segment `{sign, 0, 0}`, whose fit covers [0, 2^-7·1.125).
- |x| ≥ 2^9, inf and NaN use segment `{sign, 15, 7}`, the saturating tail.

## Evaluation

An entry is `{slope bf16 [31:16], intercept bf16 [15:0]}`. Each lane
computes `bf16(math_bf16_fma(slope, x, {icpt, 16'h0}))`: one fp32 rounding,
then RNE to bf16. An infinite `x` against a zero slope returns the
intercept — the saturating value — instead of the `0 × inf` NaN. A NaN `x`
returns NaN.

## Loading In-Band

The table is loaded through the seam itself, like everything else the tile
receives:

- `OP_PWL_LUT`, `sub_op = 0`: write entry `B[7:0]` with line A. It retires
  a zero line.
- `OP_PWL_LUT`, `sub_op = 1`: read entry `B[7:0]` back as the result line.

256 writes stream at one per clock, so a function switch costs 256 cycles.
The table is a memory (distributed RAM, no reset); it must be loaded before
the first `OP_PWL`.

## The Table Builder

`alu-infer/bin/alu_infer_pwl.py` fits each segment by least squares, rounds
the slope to bf16, and refits the intercept against the rounded slope (the
slope's rounding error dominates otherwise). It writes 256 hex words
(`--hex`) and reports the modeled error (`--report`). It also carries the
row's bit-level model, which the testbench checks the RTL against.

| Function | Domain | Max abs error | Max rel error |
|---|---|---|---|
| sigmoid | [−12, 12] | 3.8e-3 | 2.3e-2 |
| tanh | [−12, 12] | 3.3e-3 | 4.0e-3 |
| gelu | [−12, 12] | 8.2e-3 | 1.6e-2 |
| silu | [−12, 12] | 1.6e-2 | 2.1e-2 |
| exp | [−16, 4] | — | 2.9e-2 |

: Table 2.7: modeled PWL accuracy (relative error only where |f| > 2^-6)

The sigmoid and tanh errors are at bf16's output resolution near 1
(2^-8 ≈ 3.9e-3). exp is reported where softmax uses it (x − max ≤ 0): an
octave-wide segment is too coarse for exp at large |x|, and exp(−16) is
already below anything softmax keeps.

---

**Last Updated:** 2026-10-20
