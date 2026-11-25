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

# Trap and Interrupt Behavior

## The Commit Point

Every trap is taken in MEM. Memory is written in MEM and the register file in WB, so when an instruction traps in MEM the instruction in WB (older) completes and retires, and no younger instruction has touched memory, the register file or a CSR. CSR writes also happen in MEM, so a CSR write never lands under an older trap.

An exception found in ID or EX travels with its instruction as a cause code. The instruction does not access memory or write `rd` when it reaches MEM; it traps there.

## What a Trap Does at the Boundary

| Event | Effect |
|-------|--------|
| Trap (exception or interrupt) | `mepc`, `mcause`, `mtval`, `mstatus` updated; fetch from `mtvec`; the three younger instructions (in EX, ID and IF) are discarded |
| `mret` | `mstatus` updated; fetch from `mepc`; the three younger instructions discarded |
| `fence.i` | (cached: D\$ clean, then I\$ invalidate); fetch from the next PC; the three younger instructions discarded |

: Redirects committed in MEM

The trapping instruction retires on RVFI as a trap beat (`rvfi_trap = 1`, `rvfi_trap_cause` = its mcause, no register or memory effect, `rvfi_pc_wdata` = the trap vector).

## When an Interrupt Is Taken

An interrupt is sampled at MEM. A pending, enabled interrupt attaches to the valid instruction in MEM, which traps instead of executing; `mepc` is that instruction's PC, and it runs after `mret`. Three exceptions move the boundary one instruction later:

- **An M instruction is not interruptible.** It reaches MEM only with its result done (up to 33 cycles of work). The interrupt is taken on the next instruction instead, so `mepc` is the successor's PC. The cost is latency: each back-to-back M instruction can delay an interrupt by about 34 cycles. This is the simple solution kept by the owner (2026-11-24); alternatives are tracked as riscv-ip/peregrine-rv32im ISSUE-001.
- **An access already presented is not interruptible** (cached build). A load, store or `fence.i` that presented its request to the memory side while the core was held is not interrupted on the cycle the hold drops; the interrupt goes to the next instruction. This keeps a request from being withdrawn before its handshake.
- **Nothing is taken during a hold.** While `mem_wait` is high, no trap is taken. A D\$ miss therefore delays an interrupt until the access completes.

A bubble in MEM takes no interrupt; the next valid instruction to reach MEM does.

## Interrupt Latency

From an enabled interrupt line rising to the first handler instruction being fetched: the line reaches `mip` combinationally (the CLINT's timer adds one registered cycle), the interrupt attaches to the next valid instruction in MEM, and the fetch from `mtvec` is the next cycle. In the best case that is 1 to 2 cycles; it grows by the time to the next valid instruction in MEM, any hold in progress, and the M-instruction rule above.

---

**Last Updated:** 2026-11-25
