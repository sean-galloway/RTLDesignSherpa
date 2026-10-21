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

| Parameter | Default | Description |
|-----------|---------|-------------|
| `USE_DSP` | 0 | 1: the add/subtract row is `kestrel_alu_dsp`, one DSP48E1 post-adder (module-level `use_dsp`), instead of a CARRY4 chain. Measured on xc7a100t: Vivado maps a lone add/sub but not a case that also selects the bitwise rows (0 DSPs), so bitwise, shift and set-less-than stay in fabric. On the Nexys A7 it saves 42 LUTs and costs about 0.3 ns, so 0 is the default. Synthesis only: simulation, lint and formal see the same logic for both values; the ALU unit test runs both (2026-10-20). Set from the core's `ALU_USE_DSP`. |

: kestrel_alu parameters

## Operations

| `alu_op` | `y` | Notes |
|----------|-----|-------|
| ADD | `a + b` | Also computes branch/JAL targets when `a = pc` |
| SUB | `a + ~b + 1` | one adder for ADD/SUB: the inverted operand plus a carry-in |
| AND / OR / XOR | bitwise | |
| SLL | `a << shamt` | shamt = `b[4:0]` (unpriv §2.1.4.1: shift amounts use 5 bits) |
| SRL | `a >> shamt` | logical |
| SRA | `$signed(a) >>> shamt` | arithmetic |
| SLT | `{{31{1'b0}}, slt_lt}` | sets rd to 0/1 |
| SLTU | `{{31{1'b0}}, slt_lt}` | unsigned, notably for SLTIU's sign-extended-then-unsigned immediate; SLT and SLTU share one comparator, the operands extended to 33 bits with the sign bit for SLT and a zero for SLTU |

: ALU operations (`shamt = b[4:0]`)

The result is the OR of every row, each forced to zero unless its op is selected, rather than a final multiplexer (2026-10-20; the OR-combined result is an idea from the BRISKI barrel core). An undefined op yields zero.

The shift-by-`b[4:0]` matches the ISA's shamt semantics exactly — and because the decode table keys SLLI/SRLI/SRAI fully on funct7, encodings with shamt[5] set (reserved in RV32I) never reach this module as shifts; they halt as illegal in decode.

## The Flags Ruling

The flags compare `a` against `b`: `eq = (a == b)`, `lt = ($signed(a) < $signed(b))`, `ltu = (a < b)`. For branch instructions the core drives `a = pc` (the ALU is simultaneously computing `pc + imm`), so these flags would compare pc against imm — silently wrong. The core's instance leaves `eq/lt/ltu` unconnected and branches decide on the dedicated rs1/rs2 comparator in the top. The flag ports keep their own compares and stay correct (the unit test checks them); SLT/SLTU use the shared comparator instead. The flags are available to any future consumer whose `a`/`b` are the intended operands. This was a reviewed ruling (Task 4 review, SDD ledger), recorded here so nobody "fixes" the dangling pins.

---

**Last Updated:** 2026-10-07
