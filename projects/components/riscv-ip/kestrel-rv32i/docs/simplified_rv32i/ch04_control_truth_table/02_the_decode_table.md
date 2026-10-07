# The Decode Table

The full `unique casez ({opcode, funct3, funct7})` of
`rtl/fub/kestrel_decode.sv`, transcribed row for row. The key column is the
17-bit casez key written as `opcode.funct3.funct7`; `any` marks a
don't-care key field. Bundle columns show only non-default values and
are abbreviated to keep the table readable — `alu` is `alu_op`, `imm`
is `imm_sel`, `aPC` is `alu_src_a_pc`, `bImm` is `alu_src_b_imm`, `rd`
is `rd_wen`, and `dmem` reports `req`, `+we`, and the size in bytes
(B/H/W). `—` means the default value.

## Arithmetic and upper-immediate rows

The ALU computes datapath arithmetic here; for LUI the writeback mux
bypasses the ALU and takes the immediate directly (Chapter 3).

| opcode.funct3.funct7 (17-bit casez key) | Row | alu | imm | aPC | bImm | rd |
| ---------------------- | ------- | ----- | ----- | ----- | ------ | ----- |
| 0110011.000.0000000 | ADD | ADD | — | — | — | 1 |
| 0110011.000.0100000 | SUB | SUB | — | — | — | 1 |
| 0110011.001.0000000 | SLL | SLL | — | — | — | 1 |
| 0110011.010.0000000 | SLT | SLT | — | — | — | 1 |
| 0110011.011.0000000 | SLTU | SLTU | — | — | — | 1 |
| 0110011.100.0000000 | XOR | XOR | — | — | — | 1 |
| 0110011.101.0000000 | SRL | SRL | — | — | — | 1 |
| 0110011.101.0100000 | SRA | SRA | — | — | — | 1 |
| 0110011.110.0000000 | OR | OR | — | — | — | 1 |
| 0110011.111.0000000 | AND | AND | — | — | — | 1 |
| 0010011.000.any | ADDI | ADD | I | — | 1 | 1 |
| 0010011.010.any | SLTI | SLT | I | — | 1 | 1 |
| 0010011.011.any | SLTIU | SLTU | I | — | 1 | 1 |
| 0010011.100.any | XORI | XOR | I | — | 1 | 1 |
| 0010011.110.any | ORI | OR | I | — | 1 | 1 |
| 0010011.111.any | ANDI | AND | I | — | 1 | 1 |
| 0010011.001.0000000 | SLLI | SLL | I | — | 1 | 1 |
| 0010011.101.0000000 | SRLI | SRL | I | — | 1 | 1 |
| 0010011.101.0100000 | SRAI | SRA | I | — | 1 | 1 |
| 0110111.any.any | LUI | ADD | U | — | 1 | 1 |
| 0010111.any.any | AUIPC | ADD | U | 1 | 1 | 1 |

: Decode rows — OP, OP-IMM, LUI, AUIPC

## Loads, stores, branches, jumps

Every branch/jump row uses `alu = ADD` so the ALU produces
`pc + imm` for the next-PC mux while the dedicated comparator decides
taken-ness in parallel. JALR is the one jump whose ALU left input is
rs1, not PC.

| opcode.funct3.funct7 (17-bit casez key) | Row | imm | aPC | bImm | dmem | ctl |
| ---------------------- | ------- | ----- | ----- | ------ | ------------ | --------- |
| 0000011.000.any | LB | I | — | 1 | req, B | — |
| 0000011.001.any | LH | I | — | 1 | req, H | — |
| 0000011.010.any | LW | I | — | 1 | req, W | — |
| 0000011.100.any | LBU | I | — | 1 | req, B | — |
| 0000011.101.any | LHU | I | — | 1 | req, H | — |
| 0100011.000.any | SB | S | — | 1 | req+we, B | — |
| 0100011.001.any | SH | S | — | 1 | req+we, H | — |
| 0100011.010.any | SW | S | — | 1 | req+we, W | — |
| 1100011.000.any | BEQ | B | 1 | 1 | — | branch |
| 1100011.001.any | BNE | B | 1 | 1 | — | branch |
| 1100011.100.any | BLT | B | 1 | 1 | — | branch |
| 1100011.101.any | BGE | B | 1 | 1 | — | branch |
| 1100011.110.any | BLTU | B | 1 | 1 | — | branch |
| 1100011.111.any | BGEU | B | 1 | 1 | — | branch |
| 1101111.any.any | JAL | J | 1 | 1 | — | jump |
| 1100111.000.any | JALR | I | — | 1 | — | jalr |

: Decode rows — LOAD, STORE, BRANCH, JAL, JALR

## System, fence, and the default

| opcode | funct3 | imm12 | Row | Behavior (how the row retires) | `halt_cause` |
| ---------- | -------- | ------ | -------- | ------------------------------ | ------------ |
| 1110011 | 000 | 000 | ECALL | halt; RVFI trap beat | `4'h1` |
| 1110011 | 000 | 001 | EBREAK | halt; RVFI trap beat | `4'h2` |
| 1110011 | 000 | 302 | MRET | retire as NOP, pc+4 fall-through | — |
| 1110011 | 000 | other | — | illegal | `4'hF` |
| 1110011 | 001/010/011/101/110/111 | any | CSRRW/S/C + imm forms | `csr_stub`: zero readback, writes dropped | — |
| 1110011 | 100 | any | — | reserved, illegal | `4'hF` |
| 0001111 | 000 | any | FENCE | retire as NOP | — |
| 0001111 | 001 | any | FENCE.I | retire as NOP | — |
| 0001111 | 010-111 | any | — | reserved, illegal | `4'hF` |
| any unclaimed | — | — | default | illegal instruction | `4'hF` |

: Decode rows — SYSTEM, MISC-MEM, and the illegal default

## What the table teaches

Three design rulings visible in the table deserve explicit mention:

1. **Branch funct3 010/011, load/store funct3 011 and 110/111, MISC-MEM
   funct3 2-7, SYSTEM funct3 100, shift funct7 mismatches: all illegal.**
   RV32I leaves these encodings reserved (spec Volume I, sections 2.1.4
   and 2.1.6); kestrel halts on them rather than guessing. A reserved
   encoding today may become an instruction tomorrow, and silently
   executing it is how compatibility bugs are born.
2. **The CSR class is one stub row-set, not six special cases.** All six
   Zicsr forms share `csr_stub = 1; rd_wen = 1` and nothing else; the
   writeback mux owns the zero. The table stays small because the stub
   is honest about there being nothing to decode.
3. **Cause 3 appears nowhere in this table.** HALT_IALIGN is raised only
   in `kestrel_core`, which can see the resolved next PC and the branch
   decision. Decode provably cannot know — a branch's target alignment
   depends on the register operands it never evaluates. Chapter 5 gives
   the condition.

**Source:** `rtl/fub/kestrel_decode.sv` (the `unique casez` in full),
`rtl/includes/kestrel_pkg.sv` (HALT_* encodings), `rtl/top/kestrel_core.sv`
(misaligned-target halt)
