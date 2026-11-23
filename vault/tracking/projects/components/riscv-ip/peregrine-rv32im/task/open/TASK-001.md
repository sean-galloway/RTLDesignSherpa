# TASK-001: peregrine RV32IM core -- RTL, DV and targeted formal per PRD 0.2

**Priority:** P2
**Status:** open
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
