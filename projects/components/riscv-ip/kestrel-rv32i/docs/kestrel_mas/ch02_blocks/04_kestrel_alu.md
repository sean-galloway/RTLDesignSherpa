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

# kestrel_alu

## Purpose

`kestrel_alu` performs the datapath arithmetic for the core: ten operations selected by `alu_op`, operating on the source-mux outputs. It also computes `eq/lt/ltu` flags — which the core deliberately does not use for branches (see the ruling below).

## Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `op` | Input | `alu_op_e` | Operation select |
| `a` | Input | 32 | Left operand (PC or rs1, via the core's source mux) |
| `b` | Input | 32 | Right operand (immediate or rs2) |
| `y` | Output | 32 | Result |
| `eq` / `lt` / `ltu` | Output | 1 / 1 / 1 | Flags: equality, signed less-than, unsigned less-than — unconnected at the core instance |

: kestrel_alu interface

## Operations

| `alu_op` | `y` | Notes |
|----------|-----|-------|
| ADD | `a + b` | Also computes branch/JAL targets when `a = pc` |
| SUB | `a - b` | |
| AND / OR / XOR | bitwise | |
| SLL | `a << shamt` | shamt = `b[4:0]` (unpriv §2.1.4.1: shift amounts use 5 bits) |
| SRL | `a >> shamt` | logical |
| SRA | `$signed(a) >>> shamt` | arithmetic |
| SLT | `{{31{1'b0}}, lt}` | sets rd to 0/1 |
| SLTU | `{{31{1'b0}}, ltu}` | unsigned compare, notably for SLTIU's sign-extended-then-unsigned immediate |

: ALU operations (`shamt = b[4:0]`)

The shift-by-`b[4:0]` matches the ISA's shamt semantics exactly — and because the decode table keys SLLI/SRLI/SRAI fully on funct7, encodings with shamt[5] set (reserved in RV32I) never reach this module as shifts; they halt as illegal in decode.

## The Flags Ruling

The flags compare `a` against `b`: `eq = (a == b)`, `lt = ($signed(a) < $signed(b))`, `ltu = (a < b)`. For branch instructions the core drives `a = pc` (the ALU is simultaneously computing `pc + imm`), so these flags would compare pc against imm — silently wrong. The core's instance leaves `eq/lt/ltu` unconnected and branches decide on the dedicated rs1/rs2 comparator in the top. The ALU flags remain correct for SLT/SLTU's internal use (`lt`/`ltu` feed the SLT/SLTU rows) and are available to any future consumer whose `a`/`b` are the intended operands. This was a reviewed ruling (Task 4 review, SDD ledger), recorded here so nobody "fixes" the dangling pins.

---

**Last Updated:** 2026-10-07
