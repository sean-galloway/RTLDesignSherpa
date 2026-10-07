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

# Design Philosophy and Machine Organization

## Design Philosophy

Three commitments shape the microarchitecture, and every block chapter shows them landing:

1. **The datapath is FSM-free.** Classic processor control walks fetch/decode/execute/memory/writeback as states; in kestrel those phases are spatial, not temporal. Fetch is a wire off the PC register; decode is a truth table; execute is an ALU; memory access is a combinational port; writeback is a mux feeding a clocked register file. There is nothing to sequence, so there is no FSM — and no microcode, no control ROM, no phase counter. The two places a naive design would reach for an FSM — halting and the misaligned retry — are single holding flops with plain set/clear conditions.
2. **Control is an explicit truth table.** Decode is one `unique casez` keyed on `{opcode, funct3, funct7}` producing a thirteen-field control bundle. The same word always produces the same bundle; the table is small enough to read top to bottom and is transcribed in the kestrel_decode chapter.
3. **RVFI is the observation channel.** The retire port is not debug instrumentation bolted on afterward; it is the defined observation channel, present from the first vertical slice, and its aggregation rules are stated next to the assignments in the RTL and again in Chapter 4.

The discipline the suite's style brief imposes — datapath logic is truth tables and muxes; FSMs only where control is unavoidable — is what makes this core reviewable in one sitting and provable at shallow model-checking depth (riscv-formal runs at depth 6 and covers reset plus a two-cycle memory access with headroom).

## The Machine in One Picture

### Figure 1.1: kestrel datapath block diagram

![kestrel datapath block diagram](../assets/images/fig_1_1_datapath.png)

The diagram is drawn to match the RTL: the blocks are the module instances in `kestrel_core.sv`, and every named wire is a real signal in the source. State elements are the PC register, the register file, and three small holding registers described below; everything else is combinational.

## Module Inventory

| Module | File | Role | State |
|--------|------|------|-------|
| `kestrel_pkg` | `rtl/includes/kestrel_pkg.sv` | Shared enums (`alu_op_e`, `imm_sel_e`) and the halt-cause encodings | none |
| `kestrel_decode` | `rtl/fub/kestrel_decode.sv` | Combinational truth table from `{opcode, funct3, funct7}` to the control bundle | none |
| `kestrel_imm_gen` | `rtl/fub/kestrel_imm_gen.sv` | Builds the 32-bit immediate for the five formats | none |
| `kestrel_alu` | `rtl/fub/kestrel_alu.sv` | Ten operations: ADD SUB AND OR XOR SLL SRL SRA SLT SLTU | none |
| `kestrel_regfile` | `rtl/fub/kestrel_regfile.sv` | 32 x 32-bit registers, two combinational read ports, one synchronous write, x0 discarded | 32 words |
| `kestrel_core` | `rtl/top/kestrel_core.sv` | Wires the leaves together: source muxes, branch comparator, next-PC mux, writeback mux, L/S rotation, halt, RVFI | 5 elements below |
| `kestrel_mem_loader` | `rtl/fub/kestrel_mem_loader.sv` | Optional board glue: memories + AXIL slave + run control (see its chapter) | run bit, holding regs |

: Module inventory

## State Inventory

Everything kestrel remembers, outside the register file and (when integrated) the memories:

| Element | Width | Purpose | Next-state equation |
|---------|-------|---------|---------------------|
| `pc` | 32 | Program counter; resets to `RESET_ADDR` | `pc <= halt ? pc : (ls_first ? pc : next_pc)` |
| `retire_count` | 64 | RVFI retirement order: 0, 1, 2, ... | `+1` when `rvfi_valid` |
| `halt_q` | 1 | Halt holding register; latches any halt cause | `halt_q <= halt_q \| halt_now` |
| `ls_retry` | 1 | Cross-word L/S retry-cycle flag | `ls_retry <= ls_first` |
| `ls_rdata_lo` | 32 | First-word read data captured for the retry-cycle merge | captures `ls_rdata_shifted` when `ls_first` |

: The complete core state inventory, register file aside

Five state elements with one-line next-state equations are reviewable in minutes. The retry bit and the halt bit are control state only; `ls_rdata_lo` is the only place data is captured mid-instruction — a pipeline register in the most minimal sense.

## Key Interfaces at a Glance

| Interface | Width | Producer → Consumer |
|-----------|-------|---------------------|
| Control bundle | 13 fields | `kestrel_decode` → muxes, regfile, L/S datapath |
| `imm` | 32 | `kestrel_imm_gen` → source-B mux, writeback (LUI) |
| `alu_y` | 32 | `kestrel_alu` → dmem address, writeback |
| Branch flags | eq/lt/ltu | dedicated comparator → branch-cond mux → next-PC mux |
| `next_pc` | 32 | next-PC mux → PC register and `rvfi_pc_wdata` |
| `rd_wdata` | 32 | writeback mux → register file |
| RVFI bundle | 17 signals | aggregation assigns → top-level ports |

: Internal interface summary (full wiring in Chapter 3)

---

**Last Updated:** 2026-10-07
