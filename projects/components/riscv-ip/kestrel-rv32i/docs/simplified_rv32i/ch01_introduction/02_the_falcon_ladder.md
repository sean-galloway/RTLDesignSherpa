# The Falcon Ladder

## The suite

The falcon suite is a sequence of four RISC-V cores, one microarchitecture
per rung, each rung a complete, verified, documented design small enough
to hold in your head. Falcon species come in strict size order, and so do
the cores: the smallest falcon is the simplest machine.

| Rung | Core | ISA | Microarchitecture |
| --- | --- | --- | --- |
| 1 | kestrel-rv32i | RV32I | Single-cycle; the whole machine in one clock |
| 2 | merlin-rv32i | RV32I | Five-stage in-order pipeline (IF/ID/EX/MEM/WB) |
| 3 | peregrine-rv32im | RV32IM | Advanced in-order: branch prediction, traps, L1 caches, AXI master |
| 4 | gyrfalcon-rv32im | RV32IM | Out-of-order: rename, reorder buffer, reservation stations |

: The falcon ladder

### Figure 1.1: The falcon ladder, smallest to largest

![The falcon ladder: four rungs from single-cycle to out-of-order](../assets/images/fig_1_1_falcon_ladder.png)

The ladder is the point. Each rung exists to teach exactly one layer of
computer-architecture machinery, and each rung's verification story
reuses the rung below it. kestrel's decode truth table becomes merlin's
per-stage control; merlin's forwarding network becomes the baseline
peregrine speculates on top of; peregrine's precise traps become the
commit contract gyrfalcon's reorder buffer enforces.

## What each rung teaches

- **kestrel (this book).** Instruction formats, the datapath, control
  truth tables, the memory contract, and why single-cycle costs what it
  costs. Everything is visible in one cycle.
- **merlin.** Pipeline registers, RAW hazards, forwarding priority, the
  load-use bubble, and control-hazard flushes. The ISA is deliberately
  identical to kestrel's, so students diff behavior, not ISA, on the way
  up.
- **peregrine.** Speculation and the memory hierarchy: a branch predictor,
  real trap handling with precise state, and L1 caches behind an AXI
  master. The ISA grows to RV32IM.
- **gyrfalcon.** Out-of-order execution: register renaming, a reorder
  buffer, and reservation stations — the machine that hides program order.

## Why kestrel is rung 1

The suite's design rule is that you meet each concept at the smallest
machine that exhibits it. Single-cycle execution exhibits everything the
ISA promises and nothing the microarchitecture adds — the ideal baseline.
It is also the cheapest rung to verify exhaustively: a combinational core
with an RVFI port drops directly into riscv-formal's instruction-check
flow, and its traces diff cleanly against both a golden interpreter and
the spike emulator.

Two consequences shape this book. First, kestrel documents its
simplifications honestly — the CSR stubs, the FENCE NOPs, the halt
instead of trap — because rung 3 is where those simplifications get
replaced by real machinery, and the suite wants the seam visible.
Second, kestrel keeps the ISA surface identical to merlin's so the
rv32ui battery, the spike lockstep, and (adapted) the formal proofs all
carry over. A rung-1 verification investment pays off at rung 2.

**Source:** falcon-suite design spec, "Naming and placement" and
"Rung 1 — kestrel"; Patterson and Séquin, "RISC I: A Reduced Instruction
Set VLSI Computer" (ISCA 1981) — the original see-everything machine
(microarchitecture-papers.md, entry 1)
