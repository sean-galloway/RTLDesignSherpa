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

# kestrel_core Port Specification

## Overview

`kestrel_core` (`rtl/top/kestrel_core.sv`) is the deliverable top. All ports are single-clock (`clk`, active-low `rst_n`); there are no clock enables, no bus handshakes, and no wait-state inputs — the memory contract (next section) forbids them. One parameter, `RESET_ADDR`, selects the fetch address out of reset.

## Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | System clock; the whole machine retires in one `clk` period |
| `rst_n` | Input | 1 | Active-low reset (asynchronous assert, synchronous deassert via `ALWAYS_FF_RST`); PC → `RESET_ADDR`, halt/run state cleared, register file cleared |

: Clock and reset

## Instruction Memory (Fetch) Port

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `imem_addr` | Output | 32 | Fetch address, driven directly by the PC; always 4-byte aligned in operation |
| `imem_rdata` | Input | 32 | Combinational instruction word at `imem_addr`, valid in the same cycle |

: Instruction memory port

## Data Memory Port

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `dmem_req` | Output | 1 | A load or store is accessing data memory this cycle |
| `dmem_we` | Output | 1 | The access is a store (high) or a load (low) |
| `dmem_addr` | Output | 32 | Word-aligned byte address: `{alu_y[31:2], 2'b00}`; on the retry cycle the next word |
| `dmem_wstrb` | Output | 4 | Per-byte write enables, rotated into position for stores; all-zero for loads |
| `dmem_wdata` | Output | 32 | Store data rotated into the addressed byte lanes |
| `dmem_rdata` | Input | 32 | Combinational read data for loads, valid in the same cycle |

: Data memory port

## Halt Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `halt` | Output | 1 | High on the halting cycle and held high forever after (latched); freezes the PC and stops retirement |
| `halt_cause` | Output | 4 | Cause encoding for the halt in progress (`4'h1`, `4'h2`, `4'h3`, `4'hF`); see the halt table in the machine-state chapter |

: Halt outputs

## RVFI Retirement Channel

The RVFI port implements the riscv-formal retire convention (`vendor/riscv-formal/docs/rvfi.md`) with `NRET=1`. Exactly one beat retires per instruction; the halting instruction produces one final beat with `rvfi_trap=1`; the first cycle of a cross-word access produces no beat.

| Port | Direction | Width | Aggregation rule |
|------|-----------|-------|------------------|
| `rvfi_valid` | Output | 1 | `rst_n & ~halt_q & ~ls_first` — high exactly on retiring cycles |
| `rvfi_order` | Output | 64 | Retirement index: 0, 1, 2, ... in program order |
| `rvfi_pc_rdata` | Output | 32 | PC of the retiring instruction |
| `rvfi_pc_wdata` | Output | 32 | Architecturally next PC (`next_pc`); on a cause-`0x3` halt this is the misaligned target |
| `rvfi_insn` | Output | 32 | The instruction word |
| `rvfi_trap` | Output | 1 | `halt_now`: high on the single halting trap beat |
| `rvfi_rs1_addr` / `rvfi_rs2_addr` | Output | 5 + 5 | Register-file read addresses (`insn[19:15]`, `insn[24:20]`) |
| `rvfi_rs1_rdata` / `rvfi_rs2_rdata` | Output | 32 + 32 | Register-file read data; x0 reads zero naturally |
| `rvfi_rd_addr` / `rvfi_rd_wdata` | Output | 5 + 32 | Writeback destination and data; both zero when no register write retires (including all writes to x0 and all halted cycles) |
| `rvfi_mem_addr` | Output | 32 | Unaligned byte address of a load/store (`alu_y`); zero otherwise |
| `rvfi_mem_rmask` / `rvfi_mem_wmask` | Output | 4 + 4 | Byte lanes touched, packed from bit 0 relative to `rvfi_mem_addr` (a word access anywhere reports `4'b1111`) |
| `rvfi_mem_rdata` / `rvfi_mem_wdata` | Output | 32 + 32 | Assembled read data (loads) / size-truncated store data (`rs2_data & size_mask`); zero otherwise |

: RVFI retirement channel

The invariants verification checks on every run: `rvfi_order` strictly counts 0,1,2,...; first `rvfi_pc_rdata` after reset equals `RESET_ADDR`; `rvfi_rd_wdata == 0` whenever `rvfi_rd_addr == 0`; memory fields are non-zero only on the final cycle of an access.

---

**Last Updated:** 2026-10-07
