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

# The Pipelined Cycle

## One Instruction, Unhindered

| Cycle | Stage | What happens |
|-------|-------|--------------|
| n | IF | The PC indexes the predictor; the instruction word for the PC is on `imem_rdata` (read at last cycle's next PC); IF/ID captures `{pc, insn, guess}` at the edge |
| n+1 | ID | Decode, immediate, register read with the WB bypass; forwarding selects computed against the two older instructions; interlocks evaluated; `br_target`, `br_tgt_hit`, `jalr_x` computed; ID/EX captures |
| n+2 | EX | Forwarded operands; ALU or CSR read or M result; branch resolved against the guess; alignment checks; the predictor is written as the instruction leaves |
| n+3 | MEM | Trap, `mret` or `fence.i` committed, or the CSR write, or the data access issued; MEM/WB captures |
| n+4 | WB | Load aligned and extended; register written; forwarded to EX; RVFI retire |

: Stage timeline

With no hazards, a redirect-free stream retires one instruction per cycle.

## The Fetch

The PC register is updated with `pc_d`. A registered-read memory addresses itself with `imem_addr_next` (`pc_d`, `RESET_ADDR` in reset), so the word at `pc` is at its output in the cycle the PC holds it. A memory that takes `mem_wait` as its read enable addresses itself with `imem_addr_next_nw` instead (the I\$ does), which keeps `mem_wait` off the address.

## The Hold

`mem_wait` freezes the machine:

- the PC holds (`pc_d = pc`);
- IF/ID, ID/EX, EX/MEM and MEM/WB stall, and every flush is suppressed (`... & ~mem_wait`);
- the register-file write, the CSR updates, the M-unit start and consume, the predictor write and the retire counter are all gated;
- `rvfi_valid` and `dmem_req` are low.

An event that arises during a hold (a mispredict in EX, a trap in MEM) is still there when the hold drops, and acts then. The `_nw` signals (`pc_d_nw`, `mem_redirect_nw`) compute the same decisions without the `~mem_wait` term, for consumers that apply `mem_wait` themselves, so that `mem_wait` (a late signal in the cached build) reaches each consumer once and not again through the redirect (TASK-001 stage 7).

## Cycle Costs

| Cause | Bubbles | Mechanism |
|-------|---------|-----------|
| Mispredict | 2 | EX redirect flushes IF/ID and ID/EX |
| Trap, `mret`, `fence.i` | 3 | MEM redirect flushes IF/ID, ID/EX and the instruction leaving EX |
| Load-use | 1 | ID/EX takes a bubble, IF and ID hold |
| Load to branch / JALR | 1 more | See "Hazards, Forwarding and Interlocks" |
| CSR behind CSR | up to 2 | ID waits until the older CSR instruction has left MEM |
| M instruction | 33 / 1 / 2 | Hold-in-EX; EX/MEM takes bubbles |
| Memory | any | `mem_wait` |

: Where cycles go

---

**Last Updated:** 2026-11-25
