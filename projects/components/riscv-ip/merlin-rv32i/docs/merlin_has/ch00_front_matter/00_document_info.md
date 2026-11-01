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

## MERLIN-RV32I Hardware Architecture Specification

**Document Number:** MERLIN-HAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) defines the external, system-level architecture of the merlin-rv32i core: what the core is, what it implements, how it is connected, how it behaves at its boundaries, and how it is integrated into a larger system. It is written for consumers of the core and is deliberately interface-first.

**Target Audience:**
- System architects evaluating merlin for integration
- Hardware engineers embedding the core
- Software engineers writing or porting programs for the core
- Verification engineers planning core-level and system-level test coverage

**Companion Documents:**
- MERLIN-RV32I Micro-Architecture Specification (MAS) - Internal block-level implementation

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | MERLIN MAS v0.1 | Micro-Architecture Specification (companion) |
| [REF-2] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority; cited as "unpriv §N" |
| [REF-3] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-4] | MERLIN testplans (`dv/testplans/*.yaml`) | V&V scenarios and coverage cross-reference |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| CPI | Cycles per instruction |
| FUB | Functional Unit Block - leaf RTL module |
| GPR | General-purpose register (x0-x31; x0 is hard-wired zero) |
| HALT_* | Halt-cause encodings defined in `rv32i_pkg` |
| IALIGN | Instruction alignment: 32 bits for RV32I without the C extension |
| RVFI | RISC-V Formal Interface - one retire record per retired instruction |
| Trap beat | The single RVFI beat of a halting instruction (`rvfi_trap=1`) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-11-01 | seang | Initial HAS skeleton for the 5-stage pipelined RV32I core (`merlin_core`). Full prose is a follow-on task. |

: Document Revision History

---

**Last Updated:** 2026-11-01
