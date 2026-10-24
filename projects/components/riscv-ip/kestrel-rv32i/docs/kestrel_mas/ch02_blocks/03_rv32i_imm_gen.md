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

# rv32i_imm_gen

This block lives in `riscv-ip/common-rv32i` (`common-rv32i/rtl/fub/rv32i_imm_gen.sv`, since 2026-10-22) and is instantiated unchanged by both kestrel and gatling. kestrel is its reference consumer; this chapter is its documentation.

## Purpose

`rv32i_imm_gen` builds the 32-bit sign- or zero-extended immediate for the five RV32I instruction formats. It is pure combinational logic: all five formats are assembled in parallel from the instruction bits and one is picked by the major opcode `insn[6:2]` alone (2026-10-20). In RV32I the format is a function of the opcode, so the selection needs neither funct3/funct7 nor decode's `imm_sel`, and the immediate is ready as early as the register-file read; decode's `imm_sel` still exists and is tested, but the core leaves it unconnected. On block RAM the old path (decode → `imm_sel` → immediate → operand B) was the first half of the critical path.

## Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `insn` | Input | 32 | The instruction word (opcode and immediate-bearing bits) |
| `imm` | Output | 32 | The assembled immediate |

: rv32i_imm_gen interface

## Internal Structure

The immediate assembly follows the ISA's format definitions exactly (unpriv §2.1):

| Format | Assembly | Selected when `insn[6:2]` is |
|-------|----------|------------------|
| I | `{{20{insn[31]}}, insn[31:20]}` | anything else: OP-IMM, LOAD, JALR (and don't-cares) |
| S | `{{20{insn[31]}}, insn[31:25], insn[11:7]}` | STORE `01000` |
| B | `{{20{insn[31]}}, insn[7], insn[30:25], insn[11:8], 1'b0}` | BRANCH `11000` |
| U | `{insn[31:12], 12'b0}` | LUI `01101`, AUIPC `00101` |
| J | `{{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0}` | JAL `11011` |

: Immediate assembly per format

Notes for maintainers:

- B and J immediates append the implicit low zero (unpriv §2.1) in logic; no consumer may re-shift.
- U is zero-extended by construction (no sign bits) — LUI writes it directly, AUIPC adds it to the PC.
- SLTIU's famously surprising semantics (compare against the *sign-extended* immediate interpreted unsigned, unpriv §2.1.4.1) require no special handling here: the immediate is the same sign-extended value every I-format consumer gets; the ALU's unsigned less-than on it preserves the surprise exactly.

---

**Last Updated:** 2026-10-20
