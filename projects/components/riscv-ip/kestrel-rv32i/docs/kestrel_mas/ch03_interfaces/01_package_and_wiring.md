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

# Package Types and Top-Level Wiring

## kestrel_pkg

`kestrel_pkg` (`rtl/includes/kestrel_pkg.sv`) is the shared type and encoding source. It contains no state and no modules; every kestrel filelist pulls it in with `-f`, and consumers never name the package path directly.

### ALU operation enum (`alu_op_e`, 4 bits)

| Enumerator | Operation |
|------------|-----------|
| `ADD` `SUB` | add / subtract |
| `AND` `OR` `XOR` | bitwise |
| `SLL` `SRL` `SRA` | shifts (shamt = `b[4:0]`) |
| `SLT` `SLTU` | set-less-than, signed / unsigned |

: `alu_op_e` enumerators

### Immediate-format enum (`imm_sel_e`, 3 bits)

| Enumerator | Format | Assembly |
|------------|--------|----------|
| `I` | I-type | `{{20{insn[31]}}, insn[31:20]}` |
| `S` | S-type | `{{20{insn[31]}}, insn[31:25], insn[11:7]}` |
| `B` | B-type | `{{20{insn[31]}}, insn[7], insn[30:25], insn[11:8], 1'b0}` |
| `U` | U-type | `{insn[31:12], 12'b0}` |
| `J` | J-type | `{{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0}` |

: `imm_sel_e` enumerators

### Halt-cause encodings (`localparam logic [3:0]`)

| Name | Value | Raised in | Meaning |
|------|-------|-----------|---------|
| `HALT_NONE` | `4'h0` | — | running |
| `HALT_ECALL` | `4'h1` | `kestrel_decode` | ECALL |
| `HALT_EBREAK` | `4'h2` | `kestrel_decode` | EBREAK |
| `HALT_IALIGN` | `4'h3` | `kestrel_core` | taken control transfer to a non-4-aligned target |
| `HALT_ILL` | `4'hF` | `kestrel_decode` | illegal encoding (default row) |

: `HALT_*` encodings — the single source of truth shared by decode and core

The package comment records the ownership split: causes 1, 2, and `F` belong to decode; cause 3 belongs to the core because the condition needs the resolved next PC and branch decision that decode cannot see.

## Top-Level Wiring (kestrel_core)

The instance map every maintainer should be able to redraw from memory:

| Net(s) | Driver → Load | Notes |
|--------|---------------|-------|
| `insn = imem_rdata` | fetch → decode, imm_gen, regfile addrs, RVFI | `opcode = insn[6:0]`, `funct3 = insn[14:12]` |
| Control bundle (13) | `u_decode` → muxes, regfile, L/S datapath | keyed on `{opcode, funct3, funct7}` |
| `imm` | `u_imm_gen` → `alu_src_b` mux, writeback (LUI) | |
| `rs1_data` / `rs2_data` | `u_regfile` → source muxes, comparator, store-data rotators | read addrs from `insn[19:15]` / `insn[24:20]` |
| `alu_y` | `u_alu` → dmem address, writeback mux | ALU flags unconnected (ruling, kestrel_alu chapter) |
| `cmp_eq/cmp_lt/cmp_ltu` → `branch_cond` → `branch_taken` | core comparator → next-PC mux | funct3 selects the condition |
| `next_pc` | next-PC mux → PC register, `rvfi_pc_wdata` | 4-row priority mux |
| `rd_wdata` / `rd_wen_eff` | writeback mux + gates → `u_regfile` | x0 discard inside the file |
| L/S nets (`ls_*`, `dmem_*`) | core rotators → dmem pins | retry state `ls_retry`, merge register `ls_rdata_lo` |
| Halt nets (`halt_*`, `misalign_target`) | core → halt ports, `halt_q` | `halt_cause_eff = dec_halt_cause \| (misalign_target ? HALT_IALIGN : HALT_NONE)` |
| RVFI bundle (17) | core aggregation assigns → top ports | rules in Chapter 4 |

: kestrel_core internal wiring map

## Reset Discipline

All sequential logic uses the shared `reset_defs.svh` macros (`ALWAYS_FF_RST`, `RST_ASSERTED`): asynchronous assert, synchronous deassert, active-low `rst_n`. The register file clears to zeros; the PC clears to `RESET_ADDR`; `halt_q`, `ls_retry`, `ls_rdata_lo`, and `retire_count` clear to zero. The loader applies the same macros with `aresetn`, and its `core_rst_n` output is the core's actual reset in loader integrations.

---

**Last Updated:** 2026-10-07
