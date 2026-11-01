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

## MERLIN-RV32I Micro-Architecture Specification

**Document Number:** MERLIN-MAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) describes the internal implementation of the merlin-rv32i 5-stage pipelined RV32I core: the stage registers, the hazard/forwarding unit, the branch resolution and flush logic, the load-use interlock, and the RVFI retire aggregation.

**Target Audience:**
- RTL designers implementing or modifying the core
- Verification engineers writing directed tests and formal checks
- Architects comparing merlin against kestrel and future rungs

**Companion Documents:**
- MERLIN-RV32I Hardware Architecture Specification (HAS) - External view

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | MERLIN HAS v0.1 | Hardware Architecture Specification (companion) |
| [REF-2] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority |
| [REF-3] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-4] | MERLIN testplans (`dv/testplans/*.yaml`) | V&V scenarios and coverage cross-reference |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| FUB | Functional Unit Block - leaf RTL module |
| GPR | General-purpose register (x0-x31) |
| Forwarding | Bypassing a result from a later pipeline stage to an earlier one |
| Load-use | A read-after-write hazard where the producer is a load in MEM and the consumer is in EX |
| Flush | Killing an in-flight instruction by clearing its valid bit |
| RVFI | RISC-V Formal Interface retire channel |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-11-01 | seang | Initial MAS skeleton for the 5-stage pipelined RV32I core (`merlin_core`). Full prose and waveforms are a follow-on task. |

: Document Revision History

---

**Last Updated:** 2026-11-01
