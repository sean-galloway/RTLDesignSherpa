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

# kestrel_core (Top)

## Purpose

`kestrel_core` wires the four datapath leaves together and owns everything that is not a leaf: source muxes, the dedicated branch comparator, the next-PC mux, the writeback priority mux, the load/store rotation network, the halt holding register, and the RVFI aggregation assigns. It is the only module in the core with architectural state besides the register file.

## Interface

Ports are specified exhaustively in the HAS (Chapter 4 there). Internally the top exposes no hierarchy below the four leaf instances (`u_decode`, `u_imm_gen`, `u_regfile`, `u_alu`) plus its own always-blocks; the loader, when used, sits outside this module.

## Internal Structure

### Fetch

`imem_addr = pc` and `insn = imem_rdata` — fetch is a wire. The instruction is expected combinationally (the memory contract, HAS Ch. 4), or, from a registered-read memory, fetched one clock early at `imem_addr_next` — the value the PC takes at the coming edge (`RESET_ADDR` in reset), so the word at `pc` is at the RAM output for the cycle that executes it (Ch. 2.7). While the memory system holds `mem_wait` high, every state update in this chapter (PC, register write, halt latch, retire counter) is suppressed, `rvfi_valid` is low and the combinational halt is masked; `opcode = insn[6:0]` and `funct3 = insn[14:12]` fan out to decode and the L/S size/sign logic.

### Source Muxes

`alu_src_a = alu_src_a_pc ? pc : rs1_data` selects PC (AUIPC, branch targets) or rs1. `alu_src_b = alu_src_b_imm ? imm : rs2_data` selects the immediate or rs2. Register-file read addresses come straight from the instruction: `rs1 = insn[19:15]`, `rs2 = insn[24:20]`, `rd = insn[11:7]`.

### Writeback Priority Mux

`rd_wdata` is selected by a five-row priority mux:

| Priority | Condition | Value |
|----------|-----------|-------|
| 1 | `csr_stub` | `32'd0` — the CSR stub's zero writeback |
| 2 | `opcode == OPCODE_LUI` | `imm` — LUI never passes through the ALU |
| 3 | `ls_load` | `ls_load_data` — assembled, size/sign-corrected read data |
| 4 | `jump \|\| jalr` | `pc + 4` — the link value |
| 5 | default | `alu_y` |

: Writeback priority mux

The write enable is `rd_wen_eff = rd_wen & ~halt_q & ~mem_wait & ~misalign_link & ~ls_misalign`: decode's `rd_wen` qualified by the held halt, the memory wait, and the two halts an rd-writing instruction can raise (a misaligned JAL/JALR target, cause 3, and a misaligned load, cause 4). Decode sets `rd_wen` on none of its own halt rows and branches never write rd, so this equals gating with `halt` while keeping the branch comparator off the write-enable path (2026-10-20, the A7 critical path). The register file independently discards writes to x0.

### Next-PC Mux

Four rows, in priority order: JAL/JALR (`jump || jalr`) → `jalr ? (rs1_data + imm) & 32'hFFFF_FFFE : pc + imm`; taken branch (`branch_taken`) → `pc + imm`; default → `pc + 4`. `JALR_ALIGN_MASK = 32'hFFFF_FFFE` clears target bit 0 per unpriv §2.1.5.1. In a single-cycle machine the branch decision and the `pc + imm` target settle in parallel, so taken and not-taken branches cost the same cycle.

### Branch Comparator (the Ruling)

The ALU exports `eq/lt/ltu` flags, and the core's ALU instance **deliberately leaves them unconnected** (` .eq (), .lt (), .ltu ()`). The reason is a reviewed design ruling: for branches the ALU's left input is the PC (it is simultaneously computing `pc + imm` for the next-PC mux), so its internal flags would compare pc against imm, not rs1 against rs2 — silently wrong branch decisions. Branch conditions therefore come from a dedicated comparator on the register data:

- `cmp_eq = (rs1_data == rs2_data)`
- `cmp_lt = ($signed(rs1_data) < $signed(rs2_data))`
- `cmp_ltu = (rs1_data < rs2_data)`
- `branch_cond` selected from `cmp_*` by `funct3` in a `unique case` (BEQ→eq, BNE→~eq, BLT→lt, BGE→~lt, BLTU→ltu, BGEU→~ltu, default→0)
- `branch_taken = branch & branch_cond`

In a single-cycle machine this parallel evaluation is free: both the ALU result and the comparator decision are ready when the next PC is chosen.

### Load/Store Rotation Network

Accesses are naturally aligned; a misaligned one halts (cause 4 load, 5 store, Ch. 4.2). For an access at byte offset `o` with size `s`:

- **Offset:** `o = ls_offset = rs1_data[1:0] + imm[1:0]` — the address's low bits from their own two-bit add, so nothing below waits for the 32-bit ALU result.
- **Size decode:** `funct3[1:0]` (00 byte, 01 half, 10 word) → `ls_size_mask` (`0001`/`0011`/`1111`) and `ls_data_mask` (`0xFF`/`0xFFFF`/`0xFFFFFFFF`).
- **Misaligned test:** `ls_misalign = ls_active & (half ? o[0] : word ? (o != 0) : 0)`. It joins the halt causes; the store strobes are forced to zero.
- **Address:** `dmem_addr = {alu_y[31:2], 2'b00}`.
- **Store rotation:** `dmem_wdata = rs2_data << (8*o)`, `dmem_wstrb = ls_size_mask << o` (zero when misaligned or not a store).
- **Load rotation and size/sign select:** `ls_rdata_shifted = dmem_rdata >> (8*o)`; LB sign-extends from bit 7, LBU zero-extends, LH/LHU from bit 15, LW passes `dmem_rdata` through.

`dmem_req` is decode's request qualified by the internal reset and by `halt_q`, so a frozen halting instruction never repeats an access.

### Halt and PC Registers

The halt path (`halt_q`, `misalign_target`, `ls_misalign`, `halt_cause_eff`, `halt_now`) and the PC register (`pc <= pc_d`, `pc_d = (halt || mem_wait) ? pc : next_pc`, also driven out as `imem_addr_next`) with the retire counter complete the state. Their behavior is specified in Chapter 4.

---

**Last Updated:** 2026-10-20
