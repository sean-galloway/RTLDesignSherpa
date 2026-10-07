# Instruction Formats

## Six formats, one word

Every RV32I instruction is exactly one 32-bit word (spec Volume I,
sections 1.5 and 2.1.2). There is no compressed form at this rung:
IALIGN=32, so instructions are always 4-byte aligned and the low two
bits of the PC are always zero. That single fact is what makes kestrel's
instruction-side misaligned policy (Chapter 5) so crisp.

Six formats cover the thirty-seven instructions. Register fields are 5
bits; the opcode is 7 bits at [6:0]; funct3 and funct7 qualify the
operation within major opcodes.

| Bits | 31:25 | 24:20 | 19:15 | 14:12 | 11:7 | 6:0 |
| --- | --- | --- | --- | --- | --- | --- |
| R | funct7 | rs2 | rs1 | funct3 | rd | opcode |
| I | imm[11:0] | rs1 | funct3 | rd | opcode |
| S | imm[11:5] | rs2 | rs1 | funct3 | imm[4:0] | opcode |
| B | imm[12\|10:5] | rs2 | rs1 | funct3 | imm[4:1\|11] | opcode |
| U | imm[31:12] | rd | opcode | | | |
| J | imm[20\|10:1\|11\|19:12] | rd | opcode | | | |

: The six RV32I instruction formats (spec Volume I, section 2.1.2)

Formats with fewer than six fields pack the remaining bits into the
immediate, which is why U and J rows above leave cells empty.

## How kestrel decodes a format

kestrel's `kestrel_decode` keys its truth table on the triple
`{opcode, funct3, funct7}` — the exact fields that distinguish every
base instruction — and drives `imm_sel` to tell `kestrel_imm_gen` which
immediate assembly to build. The full table is Chapter 4; the format
layer is worth understanding on its own because the immediate encodings
are the least obvious part of the ISA.

## Immediate assembly

Only one of the six formats (I) has its immediate in one contiguous
slice. The others scatter immediate bits around the register fields —
an artifact of keeping register specifiers in fixed positions so the
register file can read while the immediate is still assembling (spec
Volume I, section 2.1.3, records this rationale). The built 32-bit
signed immediate for each format:

| Format | Immediate assembly | Used by |
| --- | --- | --- |
| I | sext(insn[31:20]) | ADDI, loads, JALR, shifts-by-immediate |
| S | sext({insn[31:25], insn[11:7]}) | stores |
| B | sext({insn[31], insn[7], insn[30:25], insn[11:8], 1'b0}) | branches |
| U | {insn[31:12], 12'b0} | LUI, AUIPC |
| J | sext({insn[31], insn[19:12], insn[20], insn[30:21], 1'b0}) | JAL |

: Immediate assembly per format (spec Volume I, section 2.1.3)

`sext` is sign-extension from bit 31 of the assembled value. B and J
immediates append an explicit 0 in bit 0 because branch and jump targets
are always 2-byte-aligned at minimum — and with IALIGN=32, kestrel
requires 4.

`kestrel_imm_gen` implements exactly this table: a five-way `unique
case` on `imm_sel` (the package enum `I, S, B, U, J`) with the sign bits
replicated by concatenation. U-type needs no sign extension work beyond
the shift; the spec's canonical form zero-extends the 20-bit field and
places it in the upper bits, which is what the RTL does.

## Shift immediates

RV32I encodes the shift amount for SLLI/SRLI/SRAI in the I-immediate's
low 5 bits (`insn[24:20]`, shamt), with `insn[30]` selecting arithmetic
versus logical right shift for the SR family and `insn[31:25]` required
to be `0000000` (SLLI, SRLI) or `0100000` (SRAI). kestrel's decode keys
on the full funct7 field, so any other high field is an illegal
instruction rather than a shift — matching the spec's reserved-encoding
rules (spec Volume I, section 2.1.4).

**Source:** RISC-V Instruction Set Manual, Volume I, sections 1.5, 2.1.2,
2.1.3, 2.1.4; `rtl/fub/kestrel_imm_gen.sv`, `rtl/fub/kestrel_decode.sv`
