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

# RISC-V Falcon Suite

Five independent, clean-slate RISC-V cores whose primary product is
**education**, in the same spirit as the
[pumice/scoria/andesite memory-controller line](../mem-ctrl-ip/README.md).
Each rung is a complete, verified, documented design small enough to hold
in your head; the rungs ascend in microarchitectural complexity so the
*diff between neighbors is the lesson*. Rungs do not share RTL — each
core is the cleanest possible example of its level, not the cheapest to
produce. Educational benefit over IP; no rung chases performance or
benchmarks.

Design spec (source of truth for scope, ISA, verification, packaging):
[`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`](../../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md).

## The ladder

Each rung carries a raptor-codename, real falcons first (species in strict
size order, tracking complexity). The falcon run ends at gyrfalcon — the
largest living species — so the top rung steps deliberately to mythology:
garuda, the giant divine raptor, king of birds, one past the largest falcon.
The codename is the RTL identifier prefix and the module/package prefix;
the DIRECTORY is the compound `<codename>-<isa>` form — `kestrel-rv32i`,
not `kestrel`. The bare codename is how the core is referred to in prose
("kestrel sees the whole machine in one cycle").

| Directory | Codename | ISA | Microarchitecture | Status |
|---|---|---|---|---|
| [`kestrel-rv32i/`](kestrel-rv32i/) | **kestrel** | RV32I | single-cycle | RTL complete; rv32ui battery 42/42 with spike lockstep; riscv-formal 42/42; doc book v0.1 published; board loader sim-verified |
| [`merlin-rv32i/`](merlin-rv32i/) | **merlin** | RV32I | 5-stage in-order pipeline | Planned; structure only |
| [`peregrine-rv32im/`](peregrine-rv32im/) | **peregrine** | RV32IM | advanced in-order: predictor, traps, L1 caches, AXI master | Planned; structure only |
| [`gyrfalcon-rv32im/`](gyrfalcon-rv32im/) | **gyrfalcon** | RV32IM | out-of-order capstone: rename, ROB, reservation stations | Planned; structure only |
| [`garuda-rv32imf/`](garuda-rv32imf/) | **garuda** | RV32IMF | gyrfalcon's OoO plus an FPU: FP register file + rename, fcsr precise flags, non-pipelined long-latency units | Planned; structure only (penciled in; beyond the 2026-10-06 design spec, which pins four rungs) |

### Adjacent: hive-serv

[`hive-serv/`](hive-serv/) — the SERV-based compute cluster (1 VexRiscv control
plane + 16 SERV monitor cores). Not a falcon-ladder rung: it *uses* RISC-V
cores rather than teaching one, so it lives beside the ladder rather than on
it. Re-homed from `compute-eng-ip/hive` 2026-10-10 (it was retired
2026-09-27 as an unstarted component; the re-home revives it under the
falcon suite). Spec pages only — no RTL yet.

## Goals per rung

**kestrel — see everything.** Single-cycle RV32I: PC, register file, ALU,
immediate generator, control as an explicit decode truth table, a plainly
documented combinational-read memory contract. The hovering falcon: the
whole machine is visible in one cycle — including its cost, since the
critical path *is* the machine, which is exactly the motivation for
merlin. **Delivers:** the ISA (R/I/S/B/U/J formats, the full base integer
set), the datapath, honest control logic.

**merlin — flow it.** The classic IF/ID/EX/MEM/WB pipeline on the
deliberately identical RV32I ISA, so students diff *behavior*, not ISA.
Forwarding from EX/MEM and MEM/WB with explicit priority, load-use
interlock stall, branches resolved in EX predict-not-taken with flush.
**Delivers:** pipeline registers, RAW hazards, forwarding priority, the
load-use bubble, control-hazard flushes, why branch resolution stage
matters.

**peregrine — speed it up.** Advanced in-order RV32IM: iterative
multicycle multiply/divide (the structural-hazard lesson), BTB + 2-bit
bimodal prediction with mispredict recovery, machine-mode CSRs with
precise exceptions and CLINT-shaped interrupts, split blocking
write-back L1 caches behind an AXI4 master on the repo fabric with
MonBus visibility. **Delivers:** speculation and recovery, precise
exceptions, the memory hierarchy, bus protocol — and ties the whole repo
together (memory controllers, cache IP line, AMBA fabric).

**gyrfalcon — hide everything.** Out-of-order capstone, same ISA so every
test battery carries over. Dual-issue dispatch, explicit rename map +
free list, 32-entry ROB with in-order commit, three reservation stations,
wakeup/select over common data buses, speculative dispatch with
checkpoint-restore rename rollback. **Delivers:** register renaming and
WAR/WAW elimination, the ROB as an undo log, out-of-order completion with
in-order retirement — the honest, complete OOO story.

**garuda — float it.** The RV32IMF delta on gyrfalcon's OoO: a 32-entry
FP register file with its own rename, an `fcsr` whose five accrued
exception flags (NV/DZ/OF/UF/NX) stay precise-exception-clean through the
ROB, and the repo's ieee754 fp32 arithmetic behind the reservation
stations — multi-cycle FMUL/FADD and the non-pipelined Goldschmidt FDIV /
Newton-rsqrt FSQRT (9–11 cycle class) as the long-latency-unit lesson.
Rounding hard-wired RNE; any other requested mode raises NV, keeping the
CSR story honest without a dynamic rounding-mode datapath. **Delivers:**
long-latency execution scheduling, FP architectural state, and the F-extension
ISA delta (F regs, `fcsr`, FMV/FCVT/FSGNJ/FCLASS) — consuming the math
library's `math_ieee754_2008_fp32_*` blocks end-to-end.

## Packaging (per rung, the MC-line treatment)

- **Doc book** — *Simplified RV32I: kestrel* and successors, Memory Notes
  branding, built through `bin/md_to_docx.py` to DOCX/PDF, following the
  Simplified DFI books' precedent. Each book lives in its rung's `docs/`;
  the kestrel edition is published at
  [`kestrel-rv32i/docs/simplified_rv32i/`](kestrel-rv32i/docs/simplified_rv32i/).
- **Formal** — riscv-formal-style ISA compliance where it pays: full on
  kestrel, retire-interface on merlin, targeted properties (exception
  precision, recovery, in-order commit, deadlock freedom) on
  peregrine/gyrfalcon.
- **Golden model** — spike ISS lockstep in the rds-dv cocotb framework;
  the classic `rv32ui`/`rv32um` riscv-tests batteries as the compliance
  gate.
- **Drill app** — `bin/apps/core_drills` (ddr_drills architecture):
  pipeline stage-viewer with forwarding arrows, hazard quiz,
  branch-predictor drill, and a rename/ROB viewer. App design gets its
  own doc once merlin's RTL is fixed.

## References and layout

Common primary sources (the RISC-V ISA manuals) live in
[`references/`](references/README.md) and are cited by chapter, not page.

Per-rung skeleton follows the dma-ip/stream component layout convention:
`rtl/`, `docs/`, `dv/` (cocotb + lockstep testbenches). Shared suite
doctrine lands in [`docs/`](docs/INDEX.md) as it is written. Per-rung
`PRD.md`/`CLAUDE.md` arrive with each rung's implementation plan.
