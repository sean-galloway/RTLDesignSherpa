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

# Verification Hooks and Observability

## The Three Testplan-Tracked Hooks

kestrel was built RVFI-first, and the verification architecture hangs three observable hooks off the boundary. Each maps to committed testplan scenarios:

| Hook | Signals | What it proves | Testplan anchor |
|------|---------|----------------|-----------------|
| RVFI retire channel | 17 `rvfi_*` ports | Architectural correctness: every retired beat diffed full-field against the golden interpreter `rv32i_interpreter.py` (pc, insn, order, trap, rs/rd, all four memory channels — no sampled subset, no tolerance); riscv-formal's 42 checks relate the same beats to ISA models | `kestrel_core` CORE-01..CORE-05, CORE-14; `kestrel_mem_loader` ML-07 |
| Halt observability | `halt`, `halt_cause` | Program end, cause classification, and the post-hold: the halting trap beat, then at least four cycles of `halt` raised with `rvfi_valid` low and the PC frozen | `kestrel_core` CORE-12, CORE-13 |
| Data-port watch | `dmem_req`, `dmem_addr`, `dmem_wstrb`, `dmem_wdata` | The memory contract on the pins: rotated strobes land the right bytes (TB per-byte merge), retry addressing steps one word, the tohost mailbox is observed on the store port, store-to-load visibility is single-cycle | `kestrel_core` CORE-08..CORE-11; loader ML-02/ML-05/ML-06 |

: The three testplan-tracked hooks

## Supporting Hooks

| Hook | Signals | Use |
|------|---------|-----|
| Loader reset tap | `core_rst_n` | Load-mode isolation: with `rst_n` released but `CTRL.run` still 0, the core is held, its PC parks at `RESET_ADDR`, and loader writes become visible on the core-side read port (ML-04) |
| Leaf busy taps | `o_dbg_busy_wr`, `o_dbg_busy_rd` | AXIL backpressure: B/R must hold stable under stalled `bready`/`rready` with busy asserted (ML-08) |
| Run-mode write rejection | AXIL write + readback | A loader write in run mode is dropped in logic with B OKAY — the halted core's ECALL word must not be poisoned (ML-09) |

: Supporting loader hooks

## The Consumer Stack

| Layer | Mechanism | Scope |
|-------|-----------|-------|
| Golden interpreter lockstep | `rv32i_interpreter.py` emits the same RVFI beat format as the core; the cocotb harness diffs full-field, zero tolerance | Every golden-trace test, plus the constrained-random fuzz (5 gate / 25 func / 200 full streams) |
| Spike lockstep | `spike --isa=RV32I -l` commit stream walked 1:1 against the core's (pc, insn) beats; exception records verified per beat; exit code confirms tohost==1 | Battery and fuzz at func level, using the hardware-misaligned spike 1.1.0 build |
| rv32ui battery | 42 self-checking riscv-tests programs run to the ECALL halt; verdict = x3's last writeback | 3/3 gate, 42/42 func and full |
| riscv-formal | 42 bounded-model-checking proofs (37 instruction models + reg/pc_fwd/pc_bwd/liveness/unique) against the RVFI port, depth 6, z3/smtbmc | Every RTL change; the gate that caught the misaligned-jump bug 42 directed tests missed |

: Verification consumer stack

## Cross-Reference to the Testplan Set

The six plans in `dv/testplans/` are the V&V cross-reference for both this MAS and the HAS: `kestrel_core_testplan.yaml` (18 scenarios — ISA classes, branches, loads/stores incl. the cross-word retry, system layer, battery, lockstep, fuzz, coverage closure at 94.9% line), `kestrel_mem_loader_testplan.yaml` (ML-01..ML-09), and per-FUB plans (`kestrel_alu`, `kestrel_decode`, `kestrel_imm_gen`, `kestrel_regfile`) whose directed rows pin each block's unit behavior against the chapters of this document. Coverage closure is measured across all cells (Verilator line coverage through the central cov_utils hook); regenerate with the commands recorded in each plan.

---

**Last Updated:** 2026-10-07
