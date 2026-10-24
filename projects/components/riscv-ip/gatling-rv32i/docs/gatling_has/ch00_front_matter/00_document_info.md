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


# Document Information

## GATLING-RV32ITETRAD Hardware Architecture Specification

**Document Number:** GATLING-HAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) is gatling's external contract: what a program running on a context can rely on, how the core connects to memory, and how a host loads, runs and observes the four contexts on the board. How it is built is the companion GATLING MAS.

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | GATLING MAS (`docs/gatling_mas/`) | Micro-Architecture Specification (companion) |
| [REF-2] | GATLING PRD v0.3 (`PRD.md`) | Requirements, the Xcell encoding table and the owner decisions |
| [REF-3] | The Barrel Model (`docs/barrel_model/barrel_model.md`) | Study chapter: why four contexts, with the kestrel-against-gatling measurement |
| [REF-4] | RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority; cited by section as "unpriv §N" |
| [REF-5] | RISC-V Instruction Set Manual, Volume II: Privileged Architecture (same PDF) | The CSRs and instructions gatling deliberately departs from; cited as "priv §N" |
| [REF-6] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel field semantics |
| [REF-7] | KESTREL HAS (`../kestrel-rv32i/docs/kestrel_has/`) | The ISA contract gatling inherits: halt causes, the CSR stub, FENCE as a no-op |
| [REF-8] | J. L. Hennessy and D. A. Patterson, *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2019 | Fine-grained multithreading, §3.11; the lineage from the CDC 6600 I/O processors through HEP, Tera and Niagara, Appendix M.5; cited as "H&P6 §N" |
| [REF-9] | D. A. Patterson and J. L. Hennessy, *Computer Organization and Design, RISC-V Edition*, 2nd ed., Morgan Kaufmann, 2021 | Pipeline hazards, §4.8-4.9; hardware multithreading, §6.4; cited as "P&H §N" |
| [REF-10] | S. L. Harris and D. M. Harris, *Digital Design and Computer Architecture, RISC-V Edition*, Morgan Kaufmann, 2022 | Multithreading as replicated architectural state, §7.7.7; cited as "H&H §N" |
| [REF-11] | Microarchitecture reading list (`projects/components/riscv-ip/references/microarchitecture-papers.md`), entries 16-20 | The barrel's primary sources: Thornton (CDC 6600), Smith and Jordan (HEP), Alverson et al. (Tera), Kongetira et al. (Niagara); cited as "(papers, entry N)" |

: Reference Documents

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-22 | seang | Initial HAS: the RV32I barrel with `NUM_HARTS` contexts (four by default, the tetrad), the CSR stub and the deliberate departures from the RISC-V spec (PRD 3.3), the board memory map, the figures (system context, programmer's view, address map) and the references. The ISA blocks are `riscv-ip/common-rv32i`'s, shared with kestrel. Xcell (PRD 3.1) reserved, not yet built. |

: Document Revision History

---

**Last Updated:** 2026-10-22
