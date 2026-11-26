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

# Traps, Interrupts and the Commit Point

## Why MEM

The trap is taken in MEM (Smith and Pleszkun's in-order case, PRD §4.3). Memory is written in MEM and the register file in WB. An exception found earlier travels with its instruction as `exc_cause`; when the instruction reaches MEM it does not access memory, write a CSR or write `rd`, and traps there. The instruction in WB is older and retires; nothing younger has touched memory, the register file or a CSR.

### Figure 4.2: Exceptions ride to MEM; MEM commits one event per cycle

![Trap detection and commit](../assets/graphviz/peregrine_traps.png)

**Source:** [peregrine_traps.dot](../assets/graphviz/peregrine_traps.dot)

## Detection

| Stage | Exception | Condition |
|-------|-----------|-----------|
| ID | Illegal instruction, `ecall`, `ebreak` | Decode's `halt_cause` (with `ZICSR=1` these are trap causes) |
| EX | Illegal instruction | A CSR instruction naming an unimplemented CSR, or writing a read-only one (address bits 11:10 = 11) |
| EX | Instruction address misaligned | A taken branch or JAL with `pc + imm` not word-aligned, or a JALR with `(rs1 + imm)` bit 1 set |
| EX | Load / store address misaligned | `rs1[1:0] + imm[1:0]` not aligned for a halfword or word |

: Where exceptions are detected

EX keeps one cause per instruction, in that order of precedence: decode's, then the CSR illegal, then the misaligned target, then the misaligned access. The low address bits come from their own two-bit add, off the 32-bit adder.

## The Commit

In MEM, for the valid instruction there:

- `mem_exc`: it carries an exception.
- `mem_irq = valid & ~m_op & irq_pending & ~r_mem_irq_lock`: an interrupt attaches to it. `irq_pending` is registered in `peregrine_csr` (one cycle behind the pins and enables, cleared for the cycle after a CSR write, trap or mret).
- `mem_trap = (mem_exc | mem_irq) & ~mem_wait`.
- `mem_mret` and `mem_csr_wen` require no exception and no interrupt.

If both an exception and an interrupt are present, the interrupt wins: the instruction never executed, mcause is the interrupt's, `mepc` is the instruction's PC, and after `mret` it executes again and raises its exception then.

| mcause | mtval |
|--------|-------|
| Interrupt (MEI, MSI, MTI) | 0 |
| `ecall` (11) | 0 |
| `ebreak` (3) | The PC |
| Misaligned target (0) | The resolved next PC (the target) |
| Misaligned load (4), store (6) | The access address (`alu_y`) |
| Illegal (2) | The instruction word |

: mcause and mtval selection

A trap:

1. updates `peregrine_csr` (`trap_take`: `mepc`, `mcause`, `mtval`, `mstatus`);
2. redirects the PC to `mtvec` and flushes IF/ID, ID/EX and the instruction leaving EX (`ex_mem_flush_eff`);
3. suppresses the data access (`dmem_req` needs no exception and no interrupt) and the CSR write;
4. passes to WB with `trap = 1`, `rd_wen = 0`, `is_mem = 0` and `next_pc = mtvec`, so it retires as a trap beat with no effects;
5. cancels the M unit if an M instruction was starting in EX.

`mret` redirects to `mepc` and updates `mstatus` the same way. A CSR write commits in MEM from `csr_wdata` computed in EX.

## When an Interrupt Is Taken

Interrupts are sampled at MEM: a pending, enabled interrupt attaches to the valid instruction entering MEM (precise at the oldest uncommitted instruction). Three rules move it:

**An M instruction is not interruptible.** It reaches MEM only with its result done. The first stage-2 build let the interrupt take it, discarding up to 33 cycles of work, and a timer re-raised 3 to 40 cycles after each acknowledge then caught every M instruction before it retired: a livelock, measured in the directed suite. The interrupt now goes to the next instruction; the boundary falls between the M instruction and its successor and `mepc` is the successor's PC, still precise. The cost is latency (about 34 cycles per back-to-back M instruction); kept as the simple solution (owner, 2026-11-24), alternatives in riscv-ip/peregrine-rv32im ISSUE-001.

**A presented access is not interruptible as its hold drops** (`CACHE_EN=1`). `r_mem_irq_lock` is set while the core is held with a load, store or `fence.i` in MEM that has presented its request; it is still set in the cycle the hold drops. Without it, an interrupt arriving during the hold would kill the instruction in that cycle and withdraw a request that the target had seen but not yet accepted, which the GAXI and AXI rules forbid. The `irq_lock` program aims the timer at exactly that cycle; removing the lock dropped 161 requests (TASK-001 stage 4).

**Nothing commits during a hold.** `mem_trap` is gated by `~mem_wait`; an interrupt pending during a D\$ miss is taken when the access completes (the cache is blocking).

## CSR Read-After-Write

CSR instructions read in EX and write in MEM. The CSR serialization interlock keeps a CSR instruction in ID while an older CSR instruction is in ID/EX or EX/MEM; there is no CSR forwarding. A non-CSR instruction cannot read a CSR, so no other hazard exists. The interrupt-pending decision reads `mie` and `mstatus` combinationally, so a CSR write that enables an interrupt affects the next instruction to reach MEM.

---

**Last Updated:** 2026-11-25
