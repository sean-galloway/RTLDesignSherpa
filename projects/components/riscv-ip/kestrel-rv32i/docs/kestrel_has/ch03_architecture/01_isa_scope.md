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

# ISA Scope

## Instruction-Set Coverage

kestrel implements the complete RV32I base integer instruction set — all 37 instructions — plus documented, bounded behavior for the FENCE/FENCE.I and SYSTEM opcode classes that surround the base set. The table below is the support matrix an integrator codes against; per-instruction encodings are the authority of the ISA manual (unpriv §2.1) and the decode truth table in the MAS.

| Instruction class | Instructions | Support | Notes |
|-------------------|--------------|---------|-------|
| OP (R-type ALU) | ADD SUB SLL SLT SLTU XOR SRL SRA OR AND | Full | funct7 must match; shift funct7 mismatches are illegal |
| OP-IMM (I-type ALU) | ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI | Full | SLTIU compares against the sign-extended immediate, unsigned (unpriv §2.1.4.1) |
| Loads | LB LH LW LBU LHU | Full | Effective address `rs1 + sext(imm)`; sign/zero extension per size |
| Stores | SB SH SW | Full | Byte strobes rotated into position; see memory contract |
| Branches | BEQ BNE BLT BGE BLTU BGEU | Full | Taken and not-taken both cost one cycle |
| Jumps | JAL JALR | Full | JALR masks target bit 0 (`unpriv §2.1.5.1`) |
| Upper immediates | LUI AUIPC | Full | LUI writes the immediate directly (never through the ALU) |
| FENCE / FENCE.I | FENCE FENCE.I | Retire as NOPs | No ordering hardware exists; MISC-MEM funct3 2-7 are illegal |
| ECALL / EBREAK | ECALL EBREAK | Halt | Causes `0x1` / `0x2`; the halting instruction retires as an RVFI trap beat |
| MRET | MRET | Retire as NOP (pc+4 fall-through) | The riscv-tests p-environment points `mepc` at the next instruction; pc+4 is what the test expects. This is not trap support |
| CSR class (Zicsr forms) | CSRRW CSRRS CSRRC CSRRWI CSRRSI CSRRCI | Bounded stub | `csr_stub`: reads return zero, writes drop, rd writes 0. **This is not CSR support** — there is no CSR file, no `mstatus`, no `mtvec` |
| SYSTEM reserved | SYSTEM funct3 100; SYSTEM imm12 other than ECALL/EBREAK/MRET | Illegal | Halt cause `0xF` |
| M/A/C extensions | — | Not present | These encodings fall to the illegal-instruction default |

: ISA support matrix by instruction class

## Reserved Encodings and HINTs

Every encoding not claimed by a decode row halts as an illegal instruction (cause `0xF`): branch funct3 2-3, load/store funct3 3 and 6-7, MISC-MEM funct3 2-7, SYSTEM funct3 100, SYSTEM imm12 outside ECALL/EBREAK/MRET, and shift funct7 mismatches (unpriv §§2.1.4, 2.1.6 reserve these). HINT encodings — base instructions with rd = x0 (unpriv §2.1.9) — execute as their base instruction; the x0 write is discarded, so the architectural effect is the NOP the spec recommends.

## Misaligned Data Accesses

RV32I permits, but does not require, hardware handling of misaligned loads and stores (unpriv §2.1.6). kestrel handles them in hardware: byte-lane rotation absorbs any in-word misalignment in the single cycle, and an access that crosses a word boundary (`addr[1:0] + size > 4`) takes a documented two-cycle retry — the PC holds for one cycle, a second beat issues at the next word, and the instruction retires once. Fixed cost: one cycle in-word, two crossing. A cross-word access is two word reads/writes and is not atomic, which the spec never promised.

Instruction-side misalignment is not permitted this latitude: with IALIGN=32, a taken branch, JAL, or JALR whose resolved target is not 4-byte aligned halts the core (cause `0x3`).

---

**Last Updated:** 2026-10-07
