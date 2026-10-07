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

`kestrel_core` wires the four datapath leaves together and owns everything that is not a leaf: source muxes, the dedicated branch comparator, the next-PC mux, the writeback priority mux, the load/store rotation network with its retry state, the halt holding register, and the RVFI aggregation assigns. It is the only module in the core with architectural state besides the register file.

## Interface

Ports are specified exhaustively in the HAS (Chapter 4 there). Internally the top exposes no hierarchy below the four leaf instances (`u_decode`, `u_imm_gen`, `u_regfile`, `u_alu`) plus its own always-blocks; the loader, when used, sits outside this module.

## Internal Structure

### Fetch

`imem_addr = pc` and `insn = imem_rdata` — fetch is a wire. The instruction is expected combinationally (the memory contract, HAS Ch. 4); `opcode = insn[6:0]` and `funct3 = insn[14:12]` fan out to decode and the L/S size/sign logic.

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

The write enable is `rd_wen_eff = rd_wen & ~ls_first & ~halt`: decode's `rd_wen` qualified by the cross-word retry's first cycle (a partial word must not commit early) and by halt (the cause-3 halt retires JAL/JALR encodings whose decode `rd_wen` is set, so the gate is `halt` itself, not decode). The register file independently discards writes to x0.

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

The L/S datapath implements the hardware-misaligned policy (unpriv §2.1.6 permits hardware handling; the plan records it as a decision). For an access at byte offset `o = alu_y[1:0]` with size `s` bytes:

- **Size decode:** `dmem_size` (00 byte, 01 half, 10 word) → `ls_size_bytes` (1/2/4), `ls_size_mask` (`0001`/`0011`/`1111`), `ls_data_mask` (`0xFF`/`0xFFFF`/`0xFFFFFFFF`).
- **Split arithmetic:** `ls_tail_size = 4 - o`; `ls_head_size = s - ls_tail_size`; `ls_crossing = ls_active & (o + s > 4)`; `ls_first = ls_crossing & ~ls_retry`; `ls_second = ls_retry`; `ls_single = ls_active & ~ls_crossing`.
- **Address:** `dmem_addr = ls_second ? {alu_y[31:2] + 1, 2'b00} : {alu_y[31:2], 2'b00}` — beat 2 issues at the next word.
- **Store rotation (the store rotator):** beat 1 writes `rs2_data << (8*o)` with strobe `ls_size_mask << o`; beat 2 writes `rs2_data >> (8*ls_tail_size)` with strobe `ls_head_strobe` (a head-size decode: 0/1/2/3/4 bytes → `0000`/`0001`/`0011`/`0111`/`1111`).
- **Load rotation (the load rotator):** beat 1 captures `ls_rdata_lo <= dmem_rdata >> (8*o)`; beat 2 assembles `(dmem_rdata & ls_head_mask) << (8*ls_tail_size) | (ls_rdata_lo & ls_tail_mask)`. Single-beat loads use `(dmem_rdata >> (8*o)) & ls_data_mask`.
- **Size/sign select:** `ls_load_data` from `ls_raw_rdata` per `funct3`: LB sign-extends from bit 7, LBU zero-extends, LH/LHU from bit 15, LW passes through.

`dmem_wstrb = ls_store ? (ls_second ? ls_head_strobe : ls_size_mask << o) : 4'b0000`. Bytes that would rotate past bit 31 on beat 1 are dropped by construction — beat 2 carries them. Full cycle-level behavior and the waveform are in Chapter 4.

### Halt and PC Registers

The halt path (`halt_q`, `misalign_target`, `halt_cause_eff`, `halt_now`) and the PC register (`pc <= halt ? pc : (ls_first ? pc : next_pc)`) with the retry/merge/counter flops complete the state. Their behavior is specified in Chapter 4.

---

**Last Updated:** 2026-10-07
