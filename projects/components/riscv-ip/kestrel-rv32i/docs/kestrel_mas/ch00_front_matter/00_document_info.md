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

## KESTREL-RV32I Micro-Architecture Specification

**Document Number:** KESTREL-MAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) describes how the kestrel-rv32i core is built: one section per functional block covering its purpose, interface, internal structure, and key logic; the internal interfaces between blocks; the cycle-level behavior including the misaligned retry and halt timing; the verification hooks the design exposes on purpose; and the configuration surface. It is written for implementers and maintainers of the RTL, and for reviewers who need to check the design against its specification.

The external contract — ports as an integrator wires them, memory and halt behavior, loader programming — is the companion Hardware Architecture Specification (HAS). This document assumes it.

**Target Audience:**
- RTL maintainers extending or fixing the core
- Design reviewers checking implementation against intent
- Verification engineers wiring checkers to the internal observability points
- Students reading the RTL top to bottom

**Companion Documents:**
- KESTREL-RV32I Hardware Architecture Specification (HAS) - External architecture and integration contract
- Simplified RV32I: kestrel - Tutorial-study book covering the same ground as pedagogy

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | KESTREL HAS v0.1 | Hardware Architecture Specification (companion) |
| [REF-2] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority; cited by chapter/section as "unpriv §N" |
| [REF-3] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-4] | KESTREL testplans (`dv/testplans/*.yaml`) | V&V scenarios and coverage cross-reference |
| [REF-5] | falcon-suite RTL style brief | Datapath-as-truth-tables / FSMs-only-where-unavoidable discipline |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| Beat | One memory access cycle; a cross-word access uses two beats |
| Control bundle | The thirteen-field decode output steering the datapath each cycle |
| FUB | Functional Unit Block - leaf RTL module |
| Halt holding register | `halt_q` — one bit that latches any halt cause and holds it |
| Retry bit | `ls_retry` — one bit of control state sequencing the cross-word retry |
| Rotator | The byte-lane shift network implementing rotated strobes/data for L/S |
| Trap beat | The single RVFI beat of a halting instruction (`rvfi_trap=1`) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-07 | seang | Initial MAS release; documents the as-built RTL (Tasks 1-11) including the Task-9 IALIGN halt and the Task-11 AXIL board loader |

: Document Revision History

---

**Last Updated:** 2026-10-07
