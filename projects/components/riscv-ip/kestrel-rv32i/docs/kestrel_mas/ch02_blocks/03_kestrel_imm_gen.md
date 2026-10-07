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

# kestrel_imm_gen

## Purpose

`kestrel_imm_gen` builds the 32-bit sign- or zero-extended immediate for the five RV32I instruction formats, selected by `imm_sel` from the control bundle. It is pure combinational logic — a five-row case on bit fields of `insn`.

## Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `insn` | Input | 32 | The instruction word (only immediate-bearing bits are used) |
| `sel` | Input | `imm_sel_e` | Format select from decode: I S B U J |
| `imm` | Output | 32 | The assembled immediate |

: kestrel_imm_gen interface

## Internal Structure

The immediate assembly follows the ISA's format definitions exactly (unpriv §2.1):

| `sel` | Assembly | Formats using it |
|-------|----------|------------------|
| I | `{{20{insn[31]}}, insn[31:20]}` | ADDI/SLTI/SLTIU/XORI/ORI/ANDI, loads, JALR |
| S | `{{20{insn[31]}}, insn[31:25], insn[11:7]}` | stores |
| B | `{{20{insn[31]}}, insn[7], insn[30:25], insn[11:8], 1'b0}` | branches |
| U | `{insn[31:12], 12'b0}` | LUI, AUIPC |
| J | `{{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0}` | JAL |

: Immediate assembly per format

Notes for maintainers:

- B and J immediates append the implicit low zero (unpriv §2.1) in logic; no consumer may re-shift.
- U is zero-extended by construction (no sign bits) — LUI writes it directly, AUIPC adds it to the PC.
- SLTIU's famously surprising semantics (compare against the *sign-extended* immediate interpreted unsigned, unpriv §2.1.4.1) require no special handling here: the immediate is the same sign-extended value every I-format consumer gets; the ALU's unsigned less-than on it preserves the surprise exactly.

---

**Last Updated:** 2026-10-07
