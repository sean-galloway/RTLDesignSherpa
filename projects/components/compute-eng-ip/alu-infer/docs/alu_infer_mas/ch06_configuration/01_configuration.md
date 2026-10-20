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

# Parameters, Encodings, and Open Items

## Parameters

See Table 2.1. Two kinds:

- **Latency knobs** (`ADDER_LATENCY`, `MUL_LATENCY`, `MAC_LATENCY`,
  `PIPE_DEPTH`): none of them changes behavior seen at the seam, only
  when results are offered. The tag join absorbs any combination.
- **Build-out switches** (`EN_*`): a family built out decodes as illegal.
  The lean build (all off) is the v1 bf16 ALU.

## `func_sel` Encoding

| Bits | Field | Encoding |
|------|-------|----------|
| [4:0] | opcode | Table 2.2; 23–31 unassigned (illegal) |
| [6:5] | sub_op | row-specific: min/max select, compare operand, reduce sum/max and fold, PWL write/read, CVT destination format, ALTFMT conversion |
| [8:7] | fmt | element format: 0 bf16, 1 int8, 2 fp32, 3 fp8 e4m3 |

: Table 6.1: `func_sel` fields

## `acc_ctrl` Encoding

| Value | Name | Action |
|-------|------|--------|
| 2'b00 | HOLD | bank unchanged; present it |
| 2'b01 | ACCUMULATE | MAC / REDUCE update per active lane |
| 2'b10 | CLEAR | bank ← identity (+0; −inf or INT32_MIN for max) |
| 2'b11 | DRAIN | bank unchanged; present it (or its fold) |

: Table 6.2: `acc_ctrl` encoding (accepted 2026-10-17, "works for now")

## `threshold_imm` Uses

| Row | Meaning |
|---|---|
| compare (`sub_op[0]` = 1) | threshold, as one lane of the format |
| const | the value broadcast |
| int8 MAC / REDUCE | `[4:0]` = requantize right shift of the presented view |
| CVT bf16 → int8 | quantization scale (bf16) |

: Table 6.3: immediate uses

## Filelists

`alu-infer/rtl/filelists/alu_infer_top.f` is the block's compile closure:
`alu_infer_pkg`, the `rtl/math` filelists of every instantiated block, and
the area's sources. The unit testbench compiles it.
`filelists/alu-infer_all.f` is the area lint master, the name
`rtl/make/area.mk` derives from `AREA := alu-infer`. The cell filelists
include the block's filelist for integration.

## Open Items Register

| ID | Item | State |
|----|------|-------|
| M1 | NaN/inf semantics in min/max and activations | **Recorded as built**: each library block's semantics (min/max return the non-NaN operand; relu and the activations pass NaN). Owner may override. |
| M2 | Whether library IEEE exception outputs forward into `result_flags` | Open (observability) |
| M3 | Denormal/FTZ policy | **Recorded as built**: FTZ everywhere (every block's default `SUBNORMAL_SUPPORT = 0`). Owner may override. |
| M4 | `threshold_imm` encoding | **Recorded as built**: the raw element pattern of the format (Table 6.3) |
| M5 | `result_flags` format | Closed 2026-10-17: one mask bit per lane, packed low |
| M6 | `func_sel[8:7]` disposition | **Closed by implementation 2026-10-20**: the element-format field, as the PRD roadmap planned |
| M7 | MAC presents the post-update bank in the element format; DRAIN presents without updating | Accepted 2026-10-17; extended to REDUCE and every format |
| M8 | Per-row latency values tuned on the FPGA | Open (FPGA bring-up); the latency parameters are the knobs |

: Table 6.4: open items M1–M8

---

**Last Updated:** 2026-10-20
