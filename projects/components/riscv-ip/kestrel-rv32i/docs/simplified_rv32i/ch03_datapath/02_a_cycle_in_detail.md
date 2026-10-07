# One Cycle, End to End

## The clock in one sentence

On every rising edge, kestrel writes one register-file entry (maybe),
updates the PC (unless held), and moves its bookkeeping flops — while a
combinational cloud standing between `pc` and the next edge computes
everything the next cycle needs: the fetched instruction, its decode,
the operands, the result, the memory access, the next PC, and the RVFI
record for whatever retires this cycle.

The sections below follow the data in dependency order, not file order.

## Fetch and decode

`imem_addr = pc` and `insn = imem_rdata` — the instruction memory is
expected combinationally: address in at the cycle, word out in the same
cycle (the contract is Chapter 5). Decode is the truth table of Chapter
4, keyed on `{opcode, funct3, funct7}`, producing the thirteen-field control
bundle (`alu_op`, `imm_sel`, `alu_src_a_pc`, `alu_src_b_imm`, `rd_wen`,
`dmem_req`, `dmem_we`, `dmem_size`, `branch`, `jump`, `jalr`,
`halt_cause`, `csr_stub`) plus defaults of "no operation, no halt."

## Operands and immediates

The register file reads `rs1 = insn[19:15]` and `rs2 = insn[24:20]`
combinationally; x0 reads zero because the file ties it. The immediate
generator builds one of the five format immediates under `imm_sel`. Two
muxes select the ALU inputs: `alu_src_a` is the PC (for AUIPC and
branch targets) or `rs1_data`; `alu_src_b` is the immediate or
`rs2_data`.

## Execute

The ALU computes one of ten operations. Its internal `eq/lt/ltu` flags
are deliberately left unconnected at the instance: with `src_a = PC` for
branches those flags would compare pc against imm, not rs1 against rs2.
Branch conditions come from a dedicated comparator in the core —
`cmp_eq`, `cmp_lt` (signed), `cmp_ltu` (unsigned) on the register data —
with funct3 selecting the condition in a `unique case`. In a
single-cycle machine this parallel evaluation is free: the branch
decision and the pc+imm target are both ready when the next PC is
chosen, so taken and not-taken branches cost the same cycle.

## Next-PC selection

The next-PC mux has exactly four rows:

1. JAL: `pc + imm` (J-immediate).
2. JALR: `(rs1_data + imm) & JALR_ALIGN_MASK` with
   `JALR_ALIGN_MASK = 32'hFFFF_FFFE` — bit 0 cleared, per spec Volume I,
   section 2.1.5.1.
3. Taken branch: `pc + imm` (B-immediate).
4. Fallthrough: `pc + 4`.

When taken control flow resolves to an address whose low two bits are
not `00`, the core raises HALT_IALIGN instead of updating the PC —
Chapter 5 covers the rule and why it lives in the core rather than
decode.

## Memory access

For loads and stores, `dmem_addr` is the word-aligned ALU result,
`dmem_wdata`/`dmem_wstrb` are the store data and byte enables rotated
into position, and read data is rotated back before size/sign selection
implements LB/LBU/LH/LHU/LW. Aligned and in-word-misaligned accesses
complete in the one cycle; a cross-word access holds the PC for a retry
cycle and issues a second beat at the next word. The full misaligned
story — rotation math, retry timing, RVFI encoding — is Chapter 5's.

## Writeback

`rd_wdata` is selected by a five-row priority mux:

1. `csr_stub` — hard zero (the CSR stub, Chapter 2).
2. LUI — the U-immediate, straight from the generator, never through
   the ALU.
3. Load — the assembled, sign-extended read data.
4. JAL/JALR — `pc + 4`, the link value.
5. Everything else — `alu_y`.

The write enable is `rd_wen_eff = rd_wen & ~ls_first & ~halt`: decode's
`rd_wen` qualified by the cross-word retry's first cycle (a partial word
must not commit early) and by halt (the misaligned-control-flow halt
retires JAL/JALR encodings whose decode `rd_wen` is set, so the gate is
halt itself, not decode). The register file discards writes to x0
independently.

## Two worked examples

`add x3, x1, x2`: decode selects ADD with both source muxes on registers;
the ALU's `alu_y` passes the priority mux (row 5); x3's entry is written
on the next rising edge; `next_pc = pc + 4`.

`bne x5, x6, -8` (a backward taken edge): the comparator's `~cmp_eq` is
selected by funct3; the ALU simultaneously computes `pc + imm`; the
next-PC mux row 3 wins; the PC register loads the target on the next
edge and rvfi reports a beat with `pc_wdata` equal to that target.

**Source:** `rtl/kestrel_core.sv` (fetch, source muxes, ALU instance,
comparator, next-PC mux, writeback mux); `rtl/kestrel_decode.sv`
