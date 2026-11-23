# TASK-001: peregrine RV32IM core -- RTL, DV and targeted formal per PRD 0.2

**Priority:** P2
**Status:** ACTIVE (2026-11-23; stage 1 done)
**Owner:** TBD (owner, 2026-11-23: "accept defaults on the rest, commit and
push", ruling PRD P5-P14)

## What

Build peregrine to its [PRD](../../../../../../../../projects/components/riscv-ip/peregrine-rv32im/PRD.md)
0.2. Every decision row is DECIDED; the staging is PRD §7, each stage gated
before the next:

1. **Traps first, cacheless.** merlin's pipeline copied, plus the CSR file
   (P6), trap commit at MEM, `mret`, and `rv32i_decode` gaining `M_EXT` and
   `ZICSR` parameters, both default 0 (P11). Gate: `CACHE_EN=0`, rv32ui +
   rv32mi; kestrel, merlin and gatling full suites and the common-rv32i
   unit tests unchanged.
2. **M unit** (P3, P8). Gate: rv32um, riscv-arch-test `rv32i_m/M`.
3. **Predictor** (P2, P5). Gate: predictor stress streams, `BP_EN` A/B.
4. **Caches and fabric.** `peregrine_icache` (P9), amber as D$, the AXI4
   arbiter and CLINT (P7), `fence.i` (P10). Gate: everything at
   `CACHE_EN=1`, `Zifencei`, the interrupt suite.
5. Targeted formal; riscv-formal insn checks on `CACHE_EN=0` (P12).
6. Measure amber's hit latency before stage 4 is designed around it (P13).
7. OOC timing at 100 MHz on xc7a100t-1 (P14).

## Depends on

- cache-ip/amber-mesi-l1 TASK-004 (CPU-side clean-all) for stage 4's
  `fence.i`. Stages 1-3 do not need it.

## Stage 1: traps first, cacheless (done 2026-11-23)

Owner, 2026-11-23: "continue" (after the PRD 0.2 commit).

- **Shared decoder.** `rv32i_decode` gained `M_EXT` and `ZICSR`, both
  default 0 (PRD P11). The new outputs (`m_op`, `csr_op`, `mret`) are
  connected empty in kestrel, merlin and gatling.
  - The common-rv32i unit test gained a `M_EXT=1 ZICSR=1` cell.
  - The default cell now also checks that the M encodings are illegal and
    the new outputs stay 0.
- **`peregrine_core`.** merlin's pipeline with traps committed at MEM:
  - `peregrine_csr` holds the machine-mode CSRs of P6, plus zero-entry
    PMP CSRs;
  - interrupts are sampled at MEM;
  - `mret` redirects from MEM;
  - a CSR instruction reads in EX and writes in MEM, and waits in ID
    behind an older CSR instruction.
- **DV.**
  - `test_peregrine_battery`: rv32ui and rv32mi, with spike `--priv=m`
    lockstep on the (pc, insn) stream and every trap's kind and epc.
  - `test_peregrine_irq`: a self-checking program with a registered TB
    interrupt source and a seeded random re-raise delay.
  - Every run checks that data-memory requests equal retired accesses.
  - GTKW save file with a trap group.
- **Results, from clean** (`make run-all-full-parallel`, 9/9 cells):
  - rv32ui 42/42 against spike. `ma_data` is an expected failure at
    TESTNUM 668, the same as spike's: RV32I lets misaligned loads trap.
  - rv32mi 12/16. Four are excluded for hardware P6 leaves out: `zicntr`,
    `instret_overflow` (counters), `breakpoint` (debug triggers),
    `pmpaddr` (PMP regions). Each was run once and confirmed to fail on
    that hardware first.
  - Interrupts: about 125 taken per run, 17 to 24 of them on a load or
    store, with and without random `mem_wait`.
- **Mutation checks** (restored and diffed after each):
  - An interrupted load or store still accessing memory: caught by the
    side-effect count, 796 requests against 773 retired.
  - A trapping (misaligned) access still accessing memory: 6 rv32mi
    tests and `ma_data` fail.
  - ecall reporting mcause 8 instead of 11: 53 battery images fail
    lockstep.
- **Lessons.** Handbook
  [precise-trap-checks](../../../../../../../handbook/dv/precise-trap-checks.md).

Next: stage 2, the M unit.
