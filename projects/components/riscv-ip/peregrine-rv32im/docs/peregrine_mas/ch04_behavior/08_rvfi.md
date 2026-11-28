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

# RVFI Aggregation

RVFI is driven at WB, in order, one beat per retired instruction (PRD §4.7). Trap beats are beats.

| Field | Value |
|-------|-------|
| `rvfi_valid` | `mem_wb_q.valid & ~mem_wait` (and out of reset) |
| `rvfi_order` | A 64-bit retire counter, incremented on every beat including trap beats |
| `rvfi_pc_rdata` / `rvfi_pc_wdata` | The instruction's PC / its next PC: `mtvec` after a trap (for a WB access fault the current `mtvec`), `mepc` after `mret`, the resolved next PC otherwise |
| `rvfi_insn` | The instruction word; 0 for an instruction access fault (nothing was fetched) |
| `rvfi_trap` | The instruction trapped in MEM, or (`CACHE_EN=1`) its load or store got an error response in WB (TASK-005) |
| `rvfi_rs1_addr`, `rvfi_rs2_addr` | `insn[19:15]`, `insn[24:20]` |
| `rvfi_rs1_rdata`, `rvfi_rs2_rdata` | The forwarded EX operands; for an M instruction the latched operands |
| `rvfi_rd_addr`, `rvfi_rd_wdata` | The written register and value; both 0 if no write or `rd = x0` (a trap clears `rd_wen`) |
| `rvfi_mem_addr` | The word address of a non-trapping load or store; else 0 (a load or store access fault reports no access) |
| `rvfi_mem_rmask`, `rvfi_mem_wmask` | Size mask shifted by the byte offset, for a load or a store |
| `rvfi_mem_rdata` | The whole word on `dmem_rdata` (the mask says which bytes) |
| `rvfi_mem_wdata` | `rs2` masked to the access size, shifted onto its lanes |

: RVFI fields

Observation fields beside RVFI, valid with `rvfi_valid`:

| Field | Value |
|-------|-------|
| `rvfi_trap_cause` | The committed mcause (`wb_trap_cause`, or 5 / 7 for a WB access fault), with `rvfi_trap`; 0 otherwise |
| `rvfi_bp_pred_taken`, `rvfi_bp_pred_target` | The guess the instruction was fetched with |
| `rvfi_bp_mispredict` | EX found the guess wrong |

: Observation fields

There are no `rvfi_intr` or `rvfi_csr_*` fields. riscv-formal therefore runs without CSR checks, and interrupts are checked by the directed suites and the formal `core_props` unit.

---

**Last Updated:** 2026-11-27
