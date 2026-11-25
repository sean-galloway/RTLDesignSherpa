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

# Document Information

## PEREGRINE-RV32IM Hardware Architecture Specification

**Document Number:** PEREGRINE-HAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) defines the external, system-level architecture of the peregrine-rv32im core: what it implements, how it is built into a system, how it behaves at its boundaries, what it costs in cycles and clock, and how it was verified. It describes the RTL as built at the close of riscv-ip/peregrine-rv32im TASK-001 (all seven stages, 2026-11-25).

The block internals, the cycle-level behavior and the implementation rationale are in the companion Micro-Architecture Specification (MAS).

**Target Audience:**
- System architects evaluating peregrine for integration
- Hardware engineers embedding the core or the cached `peregrine_top`
- Firmware engineers writing machine-mode software for it
- Verification engineers planning core-level and system-level coverage

**Companion Documents:**
- PEREGRINE-RV32IM Micro-Architecture Specification (MAS) - Internal block-level implementation

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | PEREGRINE MAS v0.1 | Micro-Architecture Specification (companion) |
| [REF-2] | peregrine PRD 0.2 (`projects/components/riscv-ip/peregrine-rv32im/PRD.md`) | Requirements; decision rows P1-P14 are cited as "P<n>" |
| [REF-3] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority, including the M-extension division table |
| [REF-4] | RISC-V Instruction Set Manual, Volume II: Privileged Architecture | Machine-mode CSRs, trap entry, `mret` |
| [REF-5] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-6] | amber MAS (`projects/components/cache-ip/amber-mesi-l1/`) | The data cache: CPU port, clean-all request, AXI4 master |
| [REF-7] | riscv-ip/peregrine-rv32im TASK-001 (`vault/tracking/projects/components/riscv-ip/peregrine-rv32im/task/closed/TASK-001.md`) | Build record: stage gates, measurements, mutation results |
| [REF-8] | falcon-suite design spec (`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`) | Suite scope; peregrine is rung 3 |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| BHT | Branch history table: 2-bit saturating counters indexed by the PC |
| BTB | Branch target buffer: a direct-mapped table of tag, target and an unconditional bit |
| Bubble | A pipeline slot holding no instruction (valid = 0) |
| CLINT | Core-local interruptor: `msip`, `mtimecmp` and `mtime` in the SiFive layout |
| Commit point | MEM: the stage where a trap, `mret`, a CSR write or a store takes effect |
| CPI | Cycles per instruction |
| D\$ / I\$ | Data cache (amber) / instruction cache (`peregrine_icache`) |
| GAXI | The house valid/ready request and response port amber's CPU side uses |
| Hold-in-EX | An M instruction waits in EX until its result is ready, stalling the front end |
| `mem_wait` | The core's global hold: while high, no state element updates |
| Mispredict | The fetch guess disagrees with the resolved next PC in EX |
| RVFI | RISC-V Formal Interface: one retire record per retired instruction |
| Trap beat | The RVFI beat of an instruction that trapped (`rvfi_trap = 1`) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-11-25 | seang | Initial HAS for the peregrine-rv32im core as built by TASK-001: RV32IM + Zicsr + Zifencei in machine mode, the BTB / BHT predictor, precise traps committed at MEM, the iterative M unit, the cacheless build (`CACHE_EN=0`) and the cached `peregrine_top` (I\$, amber D\$, CLINT, uncached port, AXI4 arbiter), the 18.5 ns (54.1 MHz) clock on xc7a100t-1, and the verification summary. |

: Document Revision History

---

**Last Updated:** 2026-11-25
