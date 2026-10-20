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

# Format Conversions

`OP_CVT` converts from the format in `func_sel[8:7]` to the format in
`sub_op`. `OP_ALTFMT` covers the interchange formats that are not ALU
element formats. Every conversion is an `rtl/math` converter; this is the
PRD's growth item "format conversions" plus the int8 drain.

## Lane Packing

- **Narrowing** (narrower destination lanes): line A fills the low
  destination lanes and line B the next ones. Two source lines pack one
  result line — bf16 → int8 turns four bf16 values (two lines) into one
  line of four int8.
- **Widening** (wider destination lanes): one line A yields one part of its
  lanes. `B[0]` selects the half, or `B[1:0]` the quarter for fp8 → fp32.
- **Same format**: a copy.

## Pairs

| src → dst | Converter | Packing |
|---|---|---|
| bf16 → int8 | `math_bf16_scale_to_int8`, scale = `threshold_imm` (bf16) | narrow ×2 |
| bf16 → fp32 | `math_bf16_to_fp32` | widen, half `B[0]` |
| bf16 → fp8 | `math_bf16_to_fp8_e4m3` | narrow ×2 |
| int8 → bf16 | `math_int_to_bf16` (`INT_WIDTH = 8`), unscaled | widen, half `B[0]` |
| fp32 → bf16 | `math_fp32_to_bf16` | narrow ×2 |
| fp32 → fp8 | `math_fp32_to_fp8_e4m3` | narrow ×2 (two of four lanes filled) |
| fp8 → bf16 | `math_fp8_e4m3_to_bf16` | widen, half `B[0]` |
| fp8 → fp32 | `math_fp8_e4m3_to_fp32` | widen, quarter `B[1:0]` |
| int8 ↔ fp32, int8 ↔ fp8 | none in the library | illegal |

: Table 2.8: CVT pairs

bf16 → int8 is the **int8 drain** (`math_bf16_scale_to_int8`, growth list):
it quantizes with the immediate as scale. int8 → bf16 is unscaled; the
dequantize scale is a following `OP_MUL`.

## ALTFMT (bf16 only)

| sub_op | Conversion | Packing |
|---|---|---|
| 0 | bf16 → fp16 (`math_bf16_to_fp16`) | lane for lane |
| 1 | fp16 → bf16 (`math_fp16_to_bf16`) | lane for lane |
| 2 | bf16 → fp8 e5m2 (`math_bf16_to_fp8_e5m2`) | narrow ×2 |
| 3 | fp8 e5m2 → bf16 (`math_fp8_e5m2_to_bf16`) | widen, half `B[0]` |

: Table 2.9: ALTFMT sub-ops

---

**Last Updated:** 2026-10-20
