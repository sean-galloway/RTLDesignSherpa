# The Control Bundle

## Thirteen wires out of decode

`kestrel_decode` is a pure function from the 32-bit instruction word to
a control bundle. It holds no state and no clock; the same word always
produces the same bundle. The bundle's fields:

| Field | Type | Meaning when set / value |
| --- | --- | --- |
| `alu_op` | enum | ALU operation: ADD SUB AND OR XOR SLL SRL SRA SLT SLTU |
| `imm_sel` | enum | Immediate format to build: I S B U J |
| `alu_src_a_pc` | bit | ALU left input is the PC (else rs1) |
| `alu_src_b_imm` | bit | ALU right input is the immediate (else rs2) |
| `rd_wen` | bit | The instruction writes rd this cycle |
| `dmem_req` | bit | A data-memory access is in flight |
| `dmem_we` | bit | The access is a store (else a load) |
| `dmem_size` | 2 bits | Access size: 00 byte, 01 halfword, 10 word |
| `branch` | bit | Instruction is a conditional branch |
| `jump` | bit | Instruction is JAL |
| `jalr` | bit | Instruction is JALR |
| `halt_cause` | 4 bits | Halt encoding (Chapter 2), `HALT_NONE` when running |
| `csr_stub` | bit | SYSTEM CSR class: writeback a hard zero |

: The thirteen decode outputs

## The key: opcode, funct3, funct7

The truth table is a single `unique casez` keyed on
`{opcode, funct3, funct7}` — a 17-bit key. Every RV32I instruction is
distinguished by those three fields alone, which is why the table needs
no other instruction bits at the top level. (The SYSTEM privileged row
then re-cases on `insn[31:20]`, the imm12, to split ecall/ebreak/mret
from the illegal encodings.)

Fields that carry immediate bits in some formats are keyed as
don't-cares: `F7_DC = 7'b???????` matches OP-IMM arithmetic and every
load, store, and branch row, since funct7 is immediate bits there. The
shift rows are the exception — SLLI/SRLI/SRAI key funct7 fully, which is
what makes mis-encoded shifts illegal rather than silently executed.

## The default bundle

Before the case, decode assigns a default bundle: `alu_op = ADD`,
`imm_sel = I`, every control bit clear, `halt_cause = HALT_NONE`. Each
table row then sets only what it needs — most rows touch three or four
fields. The `default:` row of the case changes exactly one field,
`halt_cause = HALT_ILL`, which is the entire illegal-instruction
mechanism. Keeping the default explicit means every encoding not claimed
by a row halts, loudly, instead of executing as something plausible.

## Reading the table

The next section gives the table in full, transcribed from
`rtl/fub/kestrel_decode.sv`. Notation is defined at the top of that
section: the 17-bit key as `opcode.funct3.funct7`, `any` for don't-care
key fields, abbreviated bundle columns (`alu`, `imm`, `aPC`, `bImm`,
`rd`), non-default values only (`—` means the default), and `dmem`
sizes in bytes (B/H/W).

**Source:** `rtl/fub/kestrel_decode.sv`, `rtl/includes/kestrel_pkg.sv`
