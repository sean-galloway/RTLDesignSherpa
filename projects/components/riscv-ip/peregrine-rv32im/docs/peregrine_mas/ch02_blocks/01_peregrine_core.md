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

# peregrine_core (top)

**Module:** `peregrine_core.sv`

## Responsibility

`peregrine_core` instantiates the pipeline registers and the functional blocks, and owns everything between them: the PC register and next-PC mux, the forwarding muxes, the branch compare and JALR target, mispredict detection, the CSR read and write-data logic, the alignment checks, the MEM-stage commit (trap, `mret`, `fence.i`, CSR write), the data-access drive, the WB load alignment and writeback mux, and the RVFI assignment. Its ports and parameters are in the HAS ("peregrine_core Port Specification").

## Instances

| Instance | Module | Stage |
|----------|--------|-------|
| `u_reset_sync` | `reset_sync` (N=3) | - |
| `u_if_id`, `u_id_ex`, `u_ex_mem`, `u_mem_wb` | `peregrine_if_id`, `_id_ex`, `_ex_mem`, `_mem_wb` | Boundaries |
| `u_decode` | `rv32i_decode` (`M_EXT=1`, `ZICSR=1`) | ID |
| `u_imm_gen` | `rv32i_imm_gen` | ID |
| `u_regfile` | `kestrel_regfile` | ID read, WB write |
| `u_hazard` | `peregrine_hazard` | ID |
| `u_alu` | `rv32i_alu` | EX |
| `u_mdu` | `peregrine_mdu` | EX |
| `u_bpred` | `peregrine_bpred` | IF lookup, EX update |
| `u_csr` | `peregrine_csr` | EX read, MEM write |

: peregrine_core instances

## Key Internal Signals

| Signal | Meaning |
|--------|---------|
| `pc`, `pc_d`, `pc_d_nw` | The PC, its next value, and its next value as if `mem_wait` were low |
| `if_pred_taken`, `if_pred_target` | The predictor's guess for the instruction at `pc` |
| `stall_lu`, `stall_ldbr`, `stall_csr`, `stall_ifid` | Load-use, second load (any consumer of a load in MEM) and CSR interlocks; their OR |
| `ex_m_stall` | An M instruction in EX whose result is not done |
| `ex_taken`, `ex_target`, `ex_next_pc` | The resolved direction, target and next PC in EX |
| `ex_mispredict`, `ex_flush` | The guess disagrees with the outcome; the EX redirect (not while an M instruction holds) |
| `ex_leaves` | The instruction in EX moves to MEM this cycle: the predictor write enable |
| `mem_exc`, `mem_irq`, `mem_trap` | An exception rides the instruction in MEM; an interrupt attaches to it; the trap commits |
| `mem_mret`, `mem_fencei`, `mem_redirect` | `mret` and `fence.i` commits; the OR of the MEM redirects |
| `mem_redirect_nw`, `mem_redirect_pc` | The MEM redirect before its `~mem_wait` gate, and its target (`mtvec`, `mepc` or the next PC) |
| `r_mem_irq_lock` | (`CACHE_EN=1`) the instruction in MEM presented its request during a hold: not interruptible as the hold drops |
| `wb_fwd_data` | The WB value: the register-file write data and the MEM/WB forward |

: Key peregrine_core signals

## The Next-PC Mux

In priority order (`pc_d_nw`; `pc_d` is `pc` while `mem_wait` is high):

1. `mem_redirect_nw` -> `mem_redirect_pc`: trap entry to `mtvec`, `mret` to `mepc`, `fence.i` to its `pc + 4`. The oldest instruction wins.
2. `ex_flush` -> `ex_next_pc`: the resolved next PC of a mispredicted instruction.
3. `stall_ifid | ex_m_stall` -> `pc`: an interlock or the M hold.
4. `if_pred_taken` -> `if_pred_target`: the predicted target.
5. otherwise `pc + 4`.

## The Flushes

| Register | Flushed when (and `~mem_wait`) |
|----------|-------------------------------|
| IF/ID | EX redirect, or MEM redirect |
| ID/EX | EX redirect, MEM redirect, or an ID interlock (the interlock bubble) unless an M instruction holds ID/EX |
| EX/MEM | MEM redirect (kills the instruction leaving EX), or an M hold (EX/MEM takes bubbles while the M instruction waits) |
| MEM/WB | never |

: Flush conditions

A flush wins over a stall in every pipeline register. While an M instruction holds, ID/EX must keep it, so the interlock bubble is suppressed there and inserted at EX/MEM instead.

---

**Last Updated:** 2026-11-25
