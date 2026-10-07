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

Four independent, clean-slate RISC-V cores whose primary product is
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

Each rung carries a falcon-codename (species in strict size order,
tracking complexity). The codename is the RTL identifier prefix and the
module/package prefix; the DIRECTORY is the compound `<codename>-<isa>`
form — `kestrel-rv32i`, not `kestrel`. The bare codename is how the core
is referred to in prose ("kestrel sees the whole machine in one cycle").

| Directory | Codename | ISA | Microarchitecture | Status |
|---|---|---|---|---|
| [`kestrel-rv32i/`](kestrel-rv32i/) | **kestrel** | RV32I | single-cycle | RTL complete; rv32ui battery 42/42 with spike lockstep; riscv-formal 42/42; doc book v0.1 published; board loader sim-verified |
| [`merlin-rv32i/`](merlin-rv32i/) | **merlin** | RV32I | 5-stage in-order pipeline | Planned; structure only |
| [`peregrine-rv32im/`](peregrine-rv32im/) | **peregrine** | RV32IM | advanced in-order: predictor, traps, L1 caches, AXI master | Planned; structure only |
| [`gyrfalcon-rv32im/`](gyrfalcon-rv32im/) | **gyrfalcon** | RV32IM | out-of-order capstone: rename, ROB, reservation stations | Planned; structure only |

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
