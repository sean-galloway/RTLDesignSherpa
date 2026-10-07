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

## KESTREL-RV32I Hardware Architecture Specification

**Document Number:** KESTREL-HAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) defines the external, system-level architecture of the kestrel-rv32i core: what the core is, what it implements, how it is connected, how it behaves at its boundaries, and how it is integrated into a larger system. It is written for consumers of the core — integrators, firmware engineers, and verification engineers — and is deliberately interface-first: ports, contracts, encodings, and sequences, with rationale where the boundary behavior is a design decision rather than an obvious default.

This document does not describe the internal microarchitecture. Block internals, cycle-level behavior, and implementation rationale live in the companion Micro-Architecture Specification (MAS).

**Target Audience:**
- System architects evaluating kestrel for integration
- Hardware engineers embedding the core and its optional board loader
- Software engineers writing or porting programs for the core
- Verification engineers planning core-level and system-level test coverage

**Companion Documents:**
- KESTREL-RV32I Micro-Architecture Specification (MAS) - Internal block-level implementation
- Simplified RV32I: kestrel - Tutorial-study book covering the same ground as pedagogy

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | KESTREL MAS v0.1 | Micro-Architecture Specification (companion) |
| [REF-2] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority; cited by chapter/section as "unpriv §N" |
| [REF-3] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-4] | KESTREL testplans (`dv/testplans/*.yaml`) | V&V scenarios and coverage cross-reference |
| [REF-5] | Simplified RV32I: kestrel v0.1 (`docs/simplified_rv32i/`) | Study book; prose source for this specification |
| [REF-6] | falcon-suite design spec (`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`) | Suite scope and packaging authority |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| AXIL | AMBA AXI4-Lite - simple single-beat AXI subset used by the board loader |
| Beat | One memory access cycle; a cross-word access uses two beats |
| CPI | Cycles per instruction |
| FUB | Functional Unit Block - leaf RTL module |
| GPR | General-purpose register (x0-x31; x0 is hard-wired zero) |
| HALT_* | kestrel halt-cause encodings defined in `kestrel_pkg` (see Table 4.3) |
| Harvard | Separate instruction and data memory ports |
| IALIGN | Instruction alignment: 32 bits for RV32I without the C extension |
| Loader | `kestrel_mem_loader` - optional AXIL-slave board glue with on-chip memories |
| RVFI | RISC-V Formal Interface - one retire record per retired instruction |
| Trap beat | The single RVFI beat of a halting instruction (`rvfi_trap=1`) |
| Unified map | Loader address map in which one address bit selects the memory array on every port |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-07 | seang | Initial HAS release; documents the as-built RTL (Tasks 1-11) including the Task-9 IALIGN halt and the Task-11 AXIL board loader |

: Document Revision History

---

**Last Updated:** 2026-10-07
