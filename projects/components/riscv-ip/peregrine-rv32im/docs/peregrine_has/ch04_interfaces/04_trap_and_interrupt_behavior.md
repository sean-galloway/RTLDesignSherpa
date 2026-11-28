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

## Bus Errors (Cached Build)

An AXI `SLVERR` or `DECERR` (RRESP or BRESP bit 1) is reported to the core as an access fault when there is an instruction to blame, and as an interrupt when there is not (riscv-ip/peregrine-rv32im TASK-005, owner decisions 2026-11-27). OKAY responses take exactly the cycles they took before.

| Source | Trap | `mcause` | `mepc` | `mtval` |
|--------|------|----------|--------|---------|
| I\$ refill | Instruction access fault, at MEM | 1 | the fetch's PC | the fetch's PC |
| Uncached load, or amber fill for a load | Load access fault | 5 | the load's PC | the access's byte address |
| Uncached store, or amber write-allocate fill (or upgrade) for a store | Store/AMO access fault | 7 | the store's PC | the access's byte address |
| amber write-back of a dirty line (eviction or `fence.i` clean) | Platform interrupt 16, imprecise | `0x8000_0010` | the interrupted instruction | 0 |

: Bus-error reports

- **Instruction access fault.** A refill with any error beat installs nothing; the fetch enters the pipeline marked as faulted, with a zero instruction word, and traps at MEM like any exception. A sequential fetch behind it in the same line faults too, without another refill; it is younger and is flushed. The next fetch of the line refills it again.
- **Load and store access faults.** The D side answers a load or store in WB (a D\$ hit's response arrives one cycle after the accept), so that is where its error is known. An error response holds the core one more cycle; the access behind it in MEM is not accepted in that cycle and has committed nothing. Then the faulting instruction retires from WB as a trap beat (no `rd` write, no memory access on RVFI) and the instruction in MEM is discarded with everything younger. This is still precise: everything older has retired and nothing younger has written memory, the register file or a CSR. The instruction discarded in MEM had already updated the branch predictor, which holds no architectural state.
- **A failed write-back.** No instruction is waiting for a write-back, so it cannot trap. amber drops the line (the data is lost), latches its address, and holds an error status until software clears it. The status is `mip.16` (enabled by `mie.16` and `mstatus.MIE`), taken at MEM on the ordinary interrupt path, with the highest priority (16 > MEI > MSI > MTI; the privileged spec lets the platform place codes 16 and up, and spike also takes them first). The custom CSR `mbuserr` (0x7C0) reads the status (see "Machine State"); a write to it clears it. A second failure while the status is held sets the overflow bit and keeps the first address.

## When an Interrupt Is Taken

An interrupt is sampled at MEM. A pending, enabled interrupt attaches to the valid instruction in MEM, which traps instead of executing; `mepc` is that instruction's PC, and it runs after `mret`.

- **A running M instruction is interrupted** (TASK-007). While an M instruction holds in EX with its unit busy and nothing older is left in MEM, a pending interrupt takes it: the unit is cancelled, nothing is written, and `mepc` is the M instruction's PC, so it runs again from the start after `mret`.
- **The first instruction after an `mret` is not interruptible** until it commits. Every return from an interrupt therefore retires at least one instruction, and an M instruction cancelled once completes on its second issue, however often the interrupt comes back.

Three exceptions move the boundary one instruction later:

- **A finished M instruction is not interruptible.** One that reaches MEM has its result done; it commits, and the interrupt is taken on the next instruction (`mepc` = the successor's PC). Finished work is never discarded.
- **An access already presented is not interruptible** (cached build). A load, store or `fence.i` that presented its request to the memory side while the core was held is not interrupted on the cycle the hold drops; the interrupt goes to the next instruction. This keeps a request from being withdrawn before its handshake.
- **Nothing is taken during a hold.** While `mem_wait` is high, no trap is taken. A D\$ miss therefore delays an interrupt until the access completes.

A bubble in MEM takes no interrupt; the next valid instruction to reach MEM does.

## Interrupt Latency

From an enabled interrupt line rising to the first handler instruction being fetched: the line reaches `mip` combinationally (the CLINT's timer adds one registered cycle), the interrupt attaches to the next valid instruction in MEM, and the fetch from `mtvec` is the next cycle. In the best case that is 1 to 2 cycles; it grows by the time to the next valid instruction in MEM and any hold in progress. M instructions add at most one M instruction: the worst case is an interrupt arriving just after an `mret` into one, which must finish first (the progress rule). Measured from the timer line to the trap beat retiring, over back-to-back divides, the bound is 40 cycles and the measured worst case 38 (mean 8.1; `test_peregrine_mext`, latency test). Holding an interrupt behind every M instruction, as the core did before TASK-007, cost about 34 cycles per back-to-back M instruction.

---

**Last Updated:** 2026-11-27
