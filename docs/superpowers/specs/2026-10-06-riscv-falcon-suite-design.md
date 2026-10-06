# RISC-V Falcon Suite — Design

**Date:** 2026-10-06
**Status:** Draft for review
**Path:** `projects/components/riscv-ip/`

## Summary

A ladder of four independent, clean-slate RISC-V cores whose primary product
is education, in the same spirit as the pumice/scoria/andesite
memory-controller line. Each rung is a complete, verified, documented design that a
student can hold in their head; the rungs ascend in microarchitectural
complexity so the *diff* between neighbors is the lesson. Rungs do not share
RTL (Approach A): each core is the cleanest possible example of its level,
not the cheapest to produce.

## Goals / non-goals

- **Goal:** teach the ISA, the microarchitecture tradeoffs, and the
  verification discipline of CPU design end to end.
- **Goal:** tie the suite into the existing ecosystem — AXI fabric, MonBus
  monitors, the cache-IP line, the `bin/apps` drill apps, the rds-dv
  verification framework, the formal/ culture.
- **Non-goal:** performance. No rung chases benchmarks; clocks/area are
  reported for curiosity, not optimized.
- **Non-goal:** Linux-capability. The ISA tops out at RV32IM + machine-mode
  traps; no MMU, no supervisor mode, no compressed instructions.

## Naming and placement

Falcon species in strict size order, one per rung:

| Rung | Core | ISA | Microarchitecture |
|------|------|-----|-------------------|
| 1 | **kestrel-rv32i** | RV32I | single-cycle |
| 2 | **merlin-rv32i** | RV32I | 5-stage in-order pipeline |
| 3 | **peregrine-rv32im** | RV32IM | advanced in-order: predictor, traps, L1 caches, AXI master |
| 4 | **gyrfalcon-rv32im** | RV32IM | out-of-order capstone: rename, ROB, reservation stations |

(Echo noted: SpaceX also flew Kestrel/Merlin engines. These are bird names
first; the suite's theme is falconry/ornithology.)

Directory layout follows the `mem-ctrl-ip/` precedent:

```
projects/components/riscv-ip/
├── README.md                suite overview: the ladder, what each rung teaches
├── kestrel-rv32i/           rtl/ docs/ dv/
├── merlin-rv32i/            rtl/ docs/ dv/
├── peregrine-rv32im/        rtl/ docs/ dv/
├── gyrfalcon-rv32im/        rtl/ docs/ dv/
├── references/              common primary sources (the RISC-V ISA manuals)
└── docs/                    suite-level: ISA quick reference, naming rationale
```

## Rung 1 — kestrel (single-cycle RV32I)

The hovering falcon: the whole machine visible in one cycle.

- **ISA:** full RV32I base — LUI, AUIPC, JAL, JALR, six branches, five
  loads, three stores, the full OP/OP-IMM set including shifts; FENCE as a
  documented NOP; ECALL/EBREAK halt into a simple trap stub (no CSR file at
  this rung).
- **Microarchitecture:** PC register, two-read/one-write register file,
  ALU, immediate generator (R/I/S/B/U/J decode), branch/jump target
  selection, and a plainly documented memory contract. Control is an
  explicit decode truth table, not an FSM — there is no time dimension to
  control yet.
- **Memory contract (open decision, default chosen):** combinational-read
  instruction and data memories (Harvard), documented plainly; the critical
  path = the whole machine, which is itself the motivation for rung 2.
- **Teaches:** instruction formats, the datapath, control truth tables, why
  single-cycle costs what it costs.
- **Verification:** riscv-formal ISA compliance (sby flow, oss-cad-suite);
  classic `rv32ui-p-*` riscv-tests battery; spike lockstep in rds-dv cocotb.
- **Packaging:** *Simplified RV32I: kestrel* doc book (Memory Notes
  branding, `bin/md_to_docx.py` → DOCX/PDF).

## Rung 2 — merlin (5-stage pipeline RV32I)

The working falcon: hazards appear, and we learn to live with them.

- **ISA:** RV32I, deliberately identical to kestrel — students diff
  *behavior*, not ISA, when moving up a rung.
- **Microarchitecture:** IF/ID/EX/MEM/WB with pipeline registers; operand
  forwarding from EX/MEM and MEM/WB into EX with explicit priority; load-use
  interlock stall; branches resolved in EX, predict-not-taken, flush on
  taken; JAL/JALR link paths. No prediction at this rung (rung 3 adds it).
- **Teaches:** pipeline registers, RAW hazards, forwarding priority, the
  load-use bubble, control-hazard flushes, why branch resolution stage
  matters.
- **Verification:** riscv-formal pipelined adaptation (retire-interface
  checks); `rv32ui` battery; directed hazard suite (forwarding matrix,
  load-use matrix, branch flush cases); spike lockstep.
- **Packaging:** *Simplified RV32I: merlin — pipelining* book.

## Rung 3 — peregrine (advanced in-order RV32IM)

The fastest falcon: speculation, traps, and the memory hierarchy.

- **ISA:** RV32I + M (iterative multicycle multiply/divide — the
  structural-hazard lesson) + machine-mode CSRs (Zicsr): mstatus, mie, mip,
  mtvec, mepc, mcause, mscratch. Exceptions: illegal instruction, ecall/
  ebreak, misaligned access. Interrupts from a CLINT-shaped stub (software,
  timer, external line), precise at the oldest instruction.
- **Microarchitecture:** merlin's pipeline extended: BTB + 2-bit bimodal
  predictor (resolution in IF/ID), mispredict recovery flush; multicycle M
  unit with busy scoreboard; split blocking write-back I$/D$; **AXI4 master**
  onto the repo fabric with MonBus visibility. Cache-IP dependency: ship a
  simple blocking L1 inside peregrine, explicitly marked as the slot the
  cache-IP line (blocking/non-blocking as planned) will replace — mirroring
  real practice, not blocking on that project's schedule.
- **Teaches:** speculation and recovery, precise exceptions, memory
  hierarchy (hit/miss, write policy), bus protocol, multicycle arithmetic.
- **Verification:** `rv32ui` + `rv32um` batteries, trap/interrupt directed
  suite, predictor stress streams; targeted formal (exception precision,
  recovery correctness). Full riscv-formal through predictor+traps is
  disproportionate — deliberately out of scope.
- **Packaging:** *Simplified RV32IM: peregrine — speculation and traps* book.

## Rung 4 — gyrfalcon (out-of-order capstone)

The largest falcon, apex of the ladder: the machine hides the program order.

- **ISA:** RV32IM + traps, identical to peregrine so every test battery
  carries over.
- **Microarchitecture (defaults chosen, parameterized where cheap):**
  dual-issue fetch/decode/dispatch; explicit rename map (32 architectural ×
  64 physical registers) + free list; ROB, 32 entries, in-order commit;
  three reservation stations (2× ALU, 1× load-store) plus the multicycle M
  unit; wakeup/select over two common data buses; speculative dispatch off
  peregrine's BTB + 2-bit predictor; rename state checkpointed at each
  branch dispatch and restored on mispredict (simplest correct rollback,
  and the honest first OOO). Exceptions precise at commit; flush squashes
  ROB, rolls back rename, restores the free list. Reuses peregrine's L1s,
  predictor, trap machinery, and AXI fabric.
- **Teaches:** register renaming and WAR/WAW elimination, the ROB as an
  undo log, out-of-order completion with in-order retirement, why rename
  rollback is the hard part of speculation.
- **Verification:** golden-model lockstep against spike with randomized
  program streams as the primary gate; targeted formal — in-order commit
  property, deadlock/livelock freedom, recovery correctness. riscv-formal
  on an OOO core is disproportionate; optional stretch goal only.
- **Packaging:** *Simplified RV32IM: gyrfalcon — out-of-order execution* book.

## Suite-wide packaging

- **Doc books:** one per rung, Memory Notes branding, `bin/md_to_docx.py`
  pipeline to DOCX/PDF, following the Simplified DFI books' precedent.
- **Drill app:** `bin/apps/core_drills` (ddr_drills architecture: packs,
  pure model layer, node test suite, cache-busted deploy) with four modes —
  pipeline stage-viewer with forwarding arrows (merlin), hazard quiz
  (merlin), branch-predictor drill (peregrine), and a rename/ROB viewer
  that watches instructions land, rename, complete out of order, and
  retire in order (gyrfalcon). The app gets its own design doc before
  implementation; its modes arrive as the rungs they visualize land.
- **Verification infrastructure:** spike ISS as the golden model throughout;
  riscv-tests batteries per ISA scope; cocotb lockstep TBs in the rds-dv
  framework; sby-based formal where it pays (rung 1 fully, rung 2 via the
  retire interface, rungs 3–4 targeted properties).

## Build order and milestones

1. **kestrel** — RTL, testbenches, rv32ui pass, riscv-formal pass, book.
   Proves the full flow end to end at the smallest scale.
2. **merlin** — RTL, hazard suite, rv32ui pass, riscv-formal pass, book.
3. **core_drills app** — own design doc, then stage-viewer + hazard quiz.
4. **peregrine** — RTL, caches, predictor, traps, batteries + targeted
   formal, book; predictor drill mode added to the app.
5. **gyrfalcon** — RTL, lockstep + targeted formal, book; ROB viewer mode.

Effort rises steeply by rung (kestrel: small; merlin: medium; peregrine:
large; gyrfalcon: very large, 2–4× peregrine). The ladder is the point —
each rung is finishable, and finishing is what makes it teachable.

## Open decisions (defaults chosen, revisit at implementation)

- Predictor: 2-bit bimodal + BTB (not 1-bit, not TAGE — teaching signal).
- D$ policy: write-back with dirty bit (write-through is the documented
  simplification escape hatch).
- kestrel memory contract: combinational-read, Harvard — documented in the
  book so the simplification is itself instructional.
- gyrfalcon: 2-wide dispatch, 32-entry ROB, 64 physical registers,
  checkpoint-restore rename rollback — parameterized where cheap.

## Dependencies

- rds-dv cocotb framework (existing) for all lockstep TBs.
- sby + oss-cad-suite (existing) for formal.
- Cache-IP line (planned, not scheduled): peregrine/gyrfalcon ship interim
  blocking L1s marked as its replacement slot.
- `axi4_monlite` wrappers (existing) for the peregrine/gyrfalcon fabric
  ports, per the cache-IP note that that IP line uses them too.
