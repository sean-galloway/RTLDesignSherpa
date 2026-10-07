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

# Halt, IALIGN, and the System Layer

## The Halt Holding Register

`halt_q` is a one-bit flop that latches any nonzero `halt_cause_eff`:

```
halt_cause_eff = dec_halt_cause | (misalign_target ? HALT_IALIGN : HALT_NONE)
halt_now       = |halt_cause_eff
halt_q         <= halt_q | halt_now
halt           = halt_q | halt_now        // visible on the first halting cycle
```

Decode raises `HALT_ECALL (1)`, `HALT_EBREAK (2)`, and `HALT_ILL (F)`; the core raises `HALT_IALIGN (3)`. Once latched:

- The PC freezes (`pc <= halt ? pc : ...`).
- Writeback is suppressed (`rd_wen_eff` and the RVFI `rd_wb` gate both use `halt`).
- Retirement stops: `rvfi_valid = rst_n & ~halt_q & ~ls_first`, and since `halt_q` latches on the halting cycle, the halting instruction itself is the last beat — a trap beat with `rvfi_trap = halt_now`.

A holding register rather than a pulse matters for verification: an external observer sampling any time after the halt sees a stable, unambiguous stopped state with the cause still on the port. The testbench samples four post-halt cycles pinning `halt` raised, `rvfi_valid` low, `rvfi_pc_rdata` frozen.

## The IALIGN Halt (Cause 3)

With IALIGN=32 — no compressed instructions — every fetch must be 4-byte aligned, and unpriv §2.1.5 requires an *instruction-address-misaligned* exception when taken control flow targets an address whose low two bits are not `00`. RISC-V's permission to handle *data* misalignment in hardware does not extend here.

The condition, visible only in the core:

```
misalign_target = (jump | jalr | branch_taken) & (next_pc[1:0] != 2'b00)
```

**Why decode cannot catch it:** for JALR the target depends on a register value; for every branch it depends on the taken decision. Decode sees neither — it produces the control bundle, not the data. `kestrel_pkg` states the ownership directly: cause 3 belongs to the core.

**The writeback subtlety.** JAL/JALR set decode's `rd_wen` — they are link instructions, and a taken JAL/JALR that *does* align must write `pc+4`. The misaligned case must not. Rather than teaching decode about alignment, the core gates both the register write and the RVFI report with `halt` itself: `rd_wen_eff = rd_wen & ~ls_first & ~halt`, `rd_wb = rd_wen & (insn[11:7] != 0) & ~halt`. The trap beat reports the misaligned target on `rvfi_pc_wdata` (it is `next_pc`), exactly what a real trap would record as the faulting address — a detail riscv-formal's checks verify explicitly.

## The System Layer: Stubs, NOPs, and Halts

The thirty-seven base instructions sit inside two opcode classes that belong to the wider system: MISC-MEM (FENCE and friends, unpriv §2.1.7; FENCE.I is Zifencei, §4.1) and SYSTEM (ECALL, EBREAK, and the Zicsr CSR instructions, §4.2; MRET is defined in the privileged Volume II). kestrel has no memory-ordering hardware, no CSR file, and no trap handler, so these classes retire through documented stubs and NOPs. Exactly what that means — including what it does *not* mean:

### FENCE and FENCE.I retire as NOPs

kestrel's imem and dmem are separate, combinational-read ports on a single-cycle core: there is no write buffer to drain, no cache to invalidate, no instruction prefetch to refetch. Fence semantics are vacuous at this rung, and decode retires FENCE (MISC-MEM funct3 000) and FENCE.I (funct3 001) as NOPs — one cycle each, no architectural effect. MISC-MEM funct3 2-7 are reserved and halt as illegal. (The one battery test whose program modifies its own instruction stream, `rv32ui-p-fence_i`, works because the *testbench memory* is a single unified array serving both ports — a testbench coherence choice, not a core feature.)

### MRET falls through

MRET (SYSTEM funct3 000, imm12 `0x302`) returns from a machine trap. It is meaningful only when traps exist — trap state, `mepc`, privilege transfers, all rung-3 machinery. kestrel retires MRET as a documented NOP-with-fall-through: the PC advances to pc+4. That choice is not arbitrary: the riscv-tests p-environment points `mepc` at the instruction following its trap stub in the configurations kestrel runs, so pc+4 is exactly what the test expects. This is stated plainly so nobody mistakes it for trap support.

### The CSR class retires as a bounded stub

The six Zicsr forms (SYSTEM funct3 001/010/011/101/110/111) retire through `csr_stub`: decode raises `csr_stub` and `rd_wen`, and the writeback mux substitutes a hard zero. Reads return zero; writes drop on the floor. SYSTEM funct3 100 is reserved and halts as illegal.

Say it plainly: **this is not CSR support.** There is no CSR file, no `mstatus`, no `mtvec`, no counters, and nothing the instructions do has architectural effect beyond a zero written to rd. The stub exists for one bounded reason: the riscv-tests p-environment preamble executes about a dozen CSR instructions plus an MRET before every test body, and without the stub the battery cannot run at all. On the battery programs the only CSR read with rd != x0 is `mhartid` (value 0), which the stub matches. Anything needing real CSR state — trap handlers, counters, feature probing — is out of contract at this rung and fails loudly either as a zero where a nonzero was expected or as a program that halts where it should have trapped. The honesty matters for the ladder: merlin inherits the same stub, and peregrine replaces it with a real machine-mode CSR file. The seam is deliberately visible in the decode table.

## Halt Timing Summary

| Cycle | `halt` | `rvfi_valid` | `rvfi_trap` | PC | Notes |
|-------|--------|--------------|-------------|----|-------|
| Last running cycle | 0 | 1 | 0 | advances | normal retirement |
| Halting cycle | 1 (immediate) | 1 | 1 | frozen from this edge | trap beat; cause on `halt_cause`; no rd/mem fields |
| All later cycles | 1 | 0 | 0 | frozen | `halt_q` holds; cause held on the port |

: Halt timing at the boundary

---

**Last Updated:** 2026-10-07
