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

# Package Types and Encodings

`peregrine_pkg` (`rtl/includes/peregrine_pkg.sv`) holds the pipeline records, the select encodings, the exception and mcause codes and the CSR addresses. It imports `rv32i_pkg` for the ALU-op enum and the halt-cause values.

## Encodings

| Name | Value | Meaning |
|------|-------|---------|
| `WB_ALU` / `WB_LOAD` / `WB_LINK` / `WB_LUI` | 0 / 1 / 2 / 3 | Writeback source (merlin's) |
| `FWD_IDEX` / `FWD_EXMEM` / `FWD_MEMWB` | 0 / 1 / 2 | Forwarding source for an EX operand |
| `EXC_NONE` | `HALT_NONE` | No exception: the bubble value |
| `EXC_ECALL`, `EXC_EBREAK`, `EXC_IALIGN`, `EXC_LALIGN`, `EXC_SALIGN`, `EXC_ILL` | `rv32i_pkg` halt causes | In-pipeline exception codes; MEM maps them to mcause |

: peregrine_pkg encodings

The in-pipeline exception codes reuse `rv32i_pkg`'s halt-cause values because decode already raises `ecall`, `ebreak` and illegal in that encoding. The mcause codes (`MCAUSE_*`) are the privileged specification's: 0, 2, 3, 4, 6, 11 for exceptions, and 3, 7, 11 with bit 31 set for MSI, MTI, MEI.

## The Pipeline Records

### `if_id_t`

| Field | Width | Kind | Meaning |
|-------|-------|------|---------|
| `pc` | 32 | payload | Fetch PC |
| `insn` | 32 | payload | Instruction word |
| `pred_taken`, `pred_target` | 1, 32 | payload | The predictor's guess for this instruction |
| `valid` | 1 | control | Not a bubble |

: if_id_t

### `id_ex_t`

| Field | Width | Kind | Meaning |
|-------|-------|------|---------|
| `pc`, `insn`, `imm` | 32 each | payload | Instruction, its PC and immediate |
| `rs1_data`, `rs2_data` | 32 each | payload | Register values read in ID (with the WB bypass) |
| `rs1_addr`, `rs2_addr`, `rd_addr` | 5 each | payload | Register fields |
| `funct3`, `alu_op`, `alu_src_a_pc`, `alu_src_b_imm`, `wb_sel` | | payload | Execute and writeback selects |
| `rd_wen`, `dmem_req`, `dmem_we` | 1 each | control | Register write, memory access, store |
| `branch`, `jump`, `jalr` | 1 each | control | Control-transfer class |
| `exc_cause` | 4 | control | Exception raised in ID |
| `csr_op` | 1 | control | CSR instruction |
| `mret`, `m_op` | 1 each | payload | `mret`; M instruction (funct3 selects the operation) |
| `pred_taken`, `pred_target` | 1, 32 | payload | The guess, carried to EX |
| `br_target` | 32 | payload | `pc + imm`: the branch or JAL target, computed in ID (stage 7) |
| `br_tgt_hit` | 1 | payload | `pred_target == br_target` |
| `jalr_x` | 32 | payload | `pred_target - imm`: a JALR guess is right iff rs1 is `jalr_x` or `jalr_x + 1` |
| `valid` | 1 | control | Not a bubble |

: id_ex_t

### `ex_mem_t`

| Field | Width | Kind | Meaning |
|-------|-------|------|---------|
| `pc`, `next_pc` | 32 each | payload | PC and resolved next PC |
| `alu_y` | 32 | payload | ALU result, the CSR's old value, the M result, or the link value; the access address for a load or store |
| `store_data` | 32 | payload | rs2 (forwarded) |
| `rd_addr`, `wb_sel`, `funct3` | | payload | Writeback destination and select; access size |
| `rd_wen`, `dmem_req`, `dmem_we`, `ls_misalign`, `exc_cause`, `csr_op` | | control | As in ID/EX; the exception now includes EX's |
| `csr_wen`, `csr_wdata` | 1, 32 | payload | The CSR write MEM commits |
| `mret`, `m_op` | 1 each | payload | `mret`; an M instruction (not interruptible) |
| `bp_pred_taken`, `bp_pred_target`, `bp_mispredict` | | payload | Prediction observation, carried to RVFI |
| `insn`, `imm`, `rs1_rdata`, `rs2_rdata` | 32 each | payload | RVFI fields (the M unit's latched operands for an M instruction) |
| `valid` | 1 | control | Not a bubble |

: ex_mem_t

### `mem_wb_t`

| Field | Width | Kind | Meaning |
|-------|-------|------|---------|
| `pc`, `next_pc` | 32 each | payload | PC; next PC (`mtvec` on a trap, `mepc` on `mret`) |
| `alu_y`, `rd_addr`, `wb_sel`, `funct3` | | payload | Writeback value, destination, select; load size and offset |
| `rd_wen` | 1 | control | Register write (cleared for a trapping instruction) |
| `trap` | 1 | control | The instruction trapped in MEM |
| `is_mem` | 1 | payload | It accessed memory (a non-trapping load or store) |
| `exc_cause` | 4 | control | Its exception code |
| `bp_pred_taken`, `bp_pred_target`, `bp_mispredict` | | payload | Prediction observation |
| `insn`, `imm`, `rs1_rdata`, `rs2_rdata` | 32 each | payload | RVFI fields |
| `valid` | 1 | control | Not a bubble |

: mem_wb_t

## The Trap Cause Beside MEM/WB

The committed mcause rides beside MEM/WB in `wb_trap_cause` (loaded whenever `mem_wait` is low), for RVFI observation only; it is reported on `rvfi_trap_cause` with a trap beat.

---

**Last Updated:** 2026-11-25
