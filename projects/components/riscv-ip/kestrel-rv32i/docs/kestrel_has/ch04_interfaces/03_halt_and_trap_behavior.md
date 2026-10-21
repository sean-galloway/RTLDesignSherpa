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

# Halt and Trap Behavior

## Halt Versus Trap

Every event RV32I routes to a trap — environment call, breakpoint, illegal instruction, instruction-address-misaligned, load/store-address-misaligned — stops kestrel instead: the core has no trap machinery, no trap vector, no `mepc`/`mtvec`, and no privilege transfer. The suite reserves real trap delivery for rung 3 (peregrine). What kestrel guarantees instead is a precise, observable stop, suitable as a program-termination and error-detection contract.

## Halt Causes

| Cause | Name | Raised in | Trigger | Spec counterpart (unpriv) |
|-------|------|-----------|---------|---------------------------|
| `4'h0` | `HALT_NONE` | — | Running (no halt) | — |
| `4'h1` | `HALT_ECALL` | `kestrel_decode` | ECALL (SYSTEM funct3 000, imm12 000) | environment-call exception (§2.1.8) |
| `4'h2` | `HALT_EBREAK` | `kestrel_decode` | EBREAK (SYSTEM funct3 000, imm12 001) | breakpoint exception (§2.1.8) |
| `4'h3` | `HALT_IALIGN` | `kestrel_core` | Taken branch/JAL/JALR resolving to `next_pc[1:0] != 2'b00` | instruction-address-misaligned exception (§2.1.5) |
| `4'h4` | `HALT_LALIGN` | `kestrel_core` | Load whose address is not naturally aligned (half at an odd byte, word off a 4-byte boundary) | load-address-misaligned exception (§2.1.6) |
| `4'h5` | `HALT_SALIGN` | `kestrel_core` | Store whose address is not naturally aligned; no bytes are written | store/AMO-address-misaligned exception (§2.1.6) |
| `4'hF` | `HALT_ILL` | `kestrel_decode` | Any encoding no decode row claims (default row) | illegal-instruction exception |

: Halt cause encodings (single source of truth: `rtl/includes/kestrel_pkg.sv`)

Cause ownership is deliberate: decode raises causes 1, 2, and `F` because it can see the encoding; only the core can raise causes 3-5 because they need the resolved next PC and branch decision, or the access address, which decode never evaluates.

## Timing Contract

1. **Detection cycle.** `halt_now` is the combinational OR of the decode cause, the core's `misalign_target` and its `ls_misalign`, masked while `mem_wait` is high. The outputs `halt` and `halt_cause` reflect it immediately (`halt = halt_q | halt_now`), so the first halting cycle is visible without waiting for a latch.
2. **Trap beat.** The halting instruction retires on the detection cycle as the final RVFI beat: `rvfi_valid=1`, `rvfi_trap=1`, no rd writeback, no memory fields. On a cause-3 halt, `rvfi_pc_wdata` carries the misaligned target — exactly what a real trap would record as the faulting address.
3. **Hold.** `halt_q` latches on the detection cycle. Afterwards, forever: the PC is frozen, writeback is suppressed, `rvfi_valid` is low, and `halt` stays raised with the cause held on `halt_cause`. Verification samples at least four post-halt cycles to pin the hold (testplan scenario CORE-12).
4. **No recovery.** The only exit from halt is reset. There is no resume address, no handler, no continue.

## Writeback Suppression Detail

JAL/JALR encodings set decode's `rd_wen` (they are link instructions), and a cause-3 halt can retire a JAL/JALR encoding; a cause-4 halt retires a load, which also sets `rd_wen`. Those are the only halts an rd-writing instruction can raise — decode sets `rd_wen` on none of its halt rows, and branches never write rd — so the writeback gate names exactly them: `rd_wen_eff = rd_wen & ~halt_q & ~mem_wait & ~misalign_link & ~ls_misalign` (2026-10-20; gating on all of `halt` put the branch comparator on the register-write enable, the A7 critical path). It is equivalent to gating with `halt`. The RVFI rd fields are gated by `halt` itself and go to zero on the trap beat. A taken, aligned JAL/JALR writes `pc+4` normally.

## ECALL as the Termination Convention

In practice ECALL is the program-termination signal: every riscv-tests program ends in the p-environment's `RVTEST_PASS`/`RVTEST_FAIL` sequence whose final ECALL halts the core. Because the halt precedes any trap-vector `sw gp, tohost`, kestrel never writes the tohost mailbox itself; the harness watches the store port for it anyway and reads the verdict from x3's last writeback (1 = pass). Integrators building loaders should treat ECALL-halt with `gp == 1` as the success contract.

---

**Last Updated:** 2026-10-07
