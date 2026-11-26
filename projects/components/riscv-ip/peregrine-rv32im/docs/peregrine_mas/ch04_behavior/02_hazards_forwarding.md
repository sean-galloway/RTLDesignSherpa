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

# Hazards, Forwarding and Interlocks

## Operand Forwarding

EX takes each operand from one of three places, chosen by the select registered beside ID/EX:

| Select | Source | Value |
|--------|--------|-------|
| `FWD_EXMEM` | The instruction in MEM | `ex_mem_q.alu_y` (ALU, CSR old value, M result or link) |
| `FWD_MEMWB` | The instruction in WB | `mem_wb_q.alu_y`, the non-load value (a load in WB is never forwarded to EX, see Load-Use) |
| `FWD_IDEX` | The register file | The value read in ID, with the WB-to-ID bypass |

: EX operand sources

EX/MEM wins over MEM/WB; x0 never forwards. The select is computed in ID, one cycle early, against the instructions in ID/EX and EX/MEM, so EX's mux selects from a flop.

The register-file read in ID bypasses a write in the same cycle: if WB writes the register ID reads (not x0), ID takes WB's value.

A load's value is **not** forwarded from WB to EX (TASK-006). Its data arrives in WB, and that forward (amber's response, through the wrapper's capture mux and the WB alignment, into the EX operand mux and the ALU) was 1.9 ns too long at 75 MHz. The load's consumers read it through the WB-to-ID bypass instead, which ends at the ID/EX register.

## Load-Use

A load in EX whose `rd` matches either source of the instruction in ID stalls IF and ID for one cycle and inserts a bubble into ID/EX (`stall_lu`). The next cycle the load is in MEM and the consumer is still in ID; its source would forward from MEM/WB, so it stalls one more cycle (`stall_ldbr`). The load is then in WB and the consumer reads its value through the WB-to-ID bypass. A load followed directly by a dependent instruction therefore costs 2 cycles; with one instruction between them, 1 (`stall_ldbr` only).

`stall_ldbr` began as merlin's load-to-branch interlock (branch and JALR operands only). TASK-006 widened it to every consumer, so the EX operand mux and the branch compare share one MEM/WB arm, `mem_wb_q.alu_y`. Kernel CPI went from 1.343 to 1.429 (+6.4%), rv32ui from 1.989 to 1.998.

## CSR Serialization

A CSR instruction reads the CSR file in EX and writes it in MEM. A CSR instruction in ID waits (`stall_csr`) while an older CSR instruction is in ID/EX or EX/MEM, so its EX read sees every older CSR write. CSR values are not forwarded (PRD P6). The CSR's old value is `rd`'s result: it replaces the ALU result in EX and forwards like any ALU result.

## Interlock Bubble Versus the M Hold

The ID interlocks insert their bubble into ID/EX. While an M instruction holds in EX, ID/EX must keep it, so the interlock bubble is suppressed there (`stall_ifid & ~ex_m_stall`) and the M hold inserts bubbles into EX/MEM instead. A mutant that let the interlock bubble overwrite the held M instruction was caught by the load-then-M-then-branch and CSR-around hazard shapes (TASK-001 stage 2).

---

**Last Updated:** 2026-11-25
