# The Instruction Set

## The thirty-seven

RV32I is thirty-seven instructions. kestrel implements all of them, plus
documented behavior for the FENCE/FENCE.I and SYSTEM opcode classes that
the base set surrounds itself with. The groups below follow the spec's
own order (Volume I, section 2.1); the right-hand column is the spec
section each group is defined in.

### Integer register-register (R-type)

| Instruction | funct3/funct7 | Operation | Spec |
| --- | --- | --- | --- |
| ADD | 000 / 0000000 | rd = rs1 + rs2 | 2.1.4.2 |
| SUB | 000 / 0100000 | rd = rs1 - rs2 | 2.1.4.2 |
| SLL | 001 / 0000000 | rd = rs1 << rs2[4:0] | 2.1.4.2 |
| SLT | 010 / 0000000 | rd = (rs1 <s rs2) ? 1 : 0 | 2.1.4.2 |
| SLTU | 011 / 0000000 | rd = (rs1 <u rs2) ? 1 : 0 | 2.1.4.2 |
| XOR | 100 / 0000000 | rd = rs1 ^ rs2 | 2.1.4.2 |
| SRL | 101 / 0000000 | rd = rs1 >>u rs2[4:0] | 2.1.4.2 |
| SRA | 101 / 0100000 | rd = rs1 >>s rs2[4:0] | 2.1.4.2 |
| OR | 110 / 0000000 | rd = rs1 \| rs2 | 2.1.4.2 |
| AND | 111 / 0000000 | rd = rs1 & rs2 | 2.1.4.2 |

: OP group: ten register-register instructions

### Integer register-immediate (I-type)

| Instruction | funct3 | Operation | Spec |
| --- | --- | --- | --- |
| ADDI | 000 | rd = rs1 + sext(imm) | 2.1.4.1 |
| SLTI | 010 | rd = (rs1 <s sext(imm)) ? 1 : 0 | 2.1.4.1 |
| SLTIU | 011 | rd = (rs1 <u sext(imm)) ? 1 : 0 | 2.1.4.1 |
| XORI | 100 | rd = rs1 ^ sext(imm) | 2.1.4.1 |
| ORI | 110 | rd = rs1 \| sext(imm) | 2.1.4.1 |
| ANDI | 111 | rd = rs1 & sext(imm) | 2.1.4.1 |
| SLLI | 001, shamt | rd = rs1 << shamt | 2.1.4.1 |
| SRLI | 101, shamt, insn[30]=0 | rd = rs1 >>u shamt | 2.1.4.1 |
| SRAI | 101, shamt, insn[30]=1 | rd = rs1 >>s shamt | 2.1.4.1 |

: OP-IMM group: nine register-immediate instructions

SLTIU compares against the sign-extended immediate interpreted
unsigned — a famously surprising detail; `sltiu rd, rs1, -1` tests
against 0xFFFFFFFF. kestrel implements it with the ALU's unsigned
less-than on the same sign-extended immediate everyone else gets, so
the surprise is preserved exactly.

### Loads and stores

| Instruction | funct3 | Size | Sign | Spec |
| --- | --- | --- | --- | --- |
| LB | 000 | byte | signed | 2.1.6 |
| LH | 001 | halfword | signed | 2.1.6 |
| LW | 010 | word | n/a | 2.1.6 |
| LBU | 100 | byte | zero | 2.1.6 |
| LHU | 101 | halfword | zero | 2.1.6 |
| SB | 000 | byte | n/a | 2.1.6 |
| SH | 001 | halfword | n/a | 2.1.6 |
| SW | 010 | word | n/a | 2.1.6 |

: LOAD and STORE groups: five loads, three stores

Effective address is rs1 + sext(imm) for both groups. Loads sign-extend
(LB, LH) or zero-extend (LBU, LHU) into rd; stores source rs2. The
memory side of these eleven instructions — alignment policy, byte
strobes, the cross-word retry — is the subject of Chapter 5.

### Branches

| Instruction | funct3 | Condition (taken when) | Spec |
| --- | --- | --- | --- |
| BEQ | 000 | rs1 == rs2 | 2.1.5.2 |
| BNE | 001 | rs1 != rs2 | 2.1.5.2 |
| BLT | 100 | rs1 <s rs2 | 2.1.5.2 |
| BGE | 101 | rs1 >=s rs2 | 2.1.5.2 |
| BLTU | 110 | rs1 <u rs2 | 2.1.5.2 |
| BGEU | 111 | rs1 >=u rs2 | 2.1.5.2 |

: BRANCH group: six conditional branches

Target is PC + sext(B-immediate), relative to the branch's own address.
Not-taken cost is identical to taken cost in a single-cycle machine —
one cycle either way — which is one of the few places kestrel is
*easier* than the spec's mental model.

### Jumps and upper immediates

| Instruction | Format | Operation | Spec |
| --- | --- | --- | --- |
| JAL | J | rd = pc+4; pc = pc + sext(imm) | 2.1.5.1 |
| JALR | I | rd = pc+4; pc = (rs1 + sext(imm)) & ~1 | 2.1.5.1 |
| LUI | U | rd = imm (upper 20 bits) | 2.1.4 |
| AUIPC | U | rd = pc + imm | 2.1.4 |

: JAL, JALR, LUI, AUIPC

JALR masks the target's bit 0 (`JALR_ALIGN_MASK = 32'hFFFF_FFFE` in the
core); with IALIGN=32, a target whose bits [1:0] are not `00` raises the
instruction-address-misaligned halt instead of executing (Chapter 5).
AUIPC forms the first half of the standard `auipc`/`jalr` pair for
position-independent long jumps; LUI never passes through the ALU in
kestrel — the writeback mux takes the immediate directly.

## Reserved encodings

Every encoding not listed above — branch funct3 2-3, load/store funct3
3 and 6-7, MISC-MEM funct3 2-7, SYSTEM funct3 100, SYSTEM imm12 outside
ECALL/EBREAK/MRET, shift funct7 mismatches — is an illegal instruction in
kestrel: decode falls to the default row and the core halts with cause
`4'hF` (Chapter 4 gives the table; Chapter 5 explains the halt).
HINT encodings (base instructions writing x0, spec Volume I, section
2.1.9) execute as their base instruction; the x0 write is discarded, so
the architectural effect is the NOP the spec recommends.

**Source:** RISC-V Instruction Set Manual, Volume I, sections 2.1.4,
2.1.5, 2.1.6, 2.1.9; `rtl/fub/kestrel_decode.sv`, `rtl/top/kestrel_core.sv`
