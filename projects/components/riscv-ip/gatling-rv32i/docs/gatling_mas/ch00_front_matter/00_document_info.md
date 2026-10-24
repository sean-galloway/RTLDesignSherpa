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

## GATLING-RV32ITETRAD Micro-Architecture Specification

**Document Number:** GATLING-MAS-001
**Version:** 0.1
**Status:** Draft
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) describes how gatling, the four-context barrel RV32I, is built: the rotation that interleaves four hardware contexts through one F/D/X/W datapath, the context register files, the block-RAM memory system with one bank per context, per-context halts and run control, and how the design is verified. It is written for implementers and maintainers of the RTL and for reviewers checking it against the PRD.

The ISA and halt contract are kestrel's, and gatling uses kestrel's decode, immediate generator and ALU unchanged; their internals are in the KESTREL MAS and are not repeated here. The external contract is the companion GATLING HAS.

**Companion Documents:**
- GATLING-RV32ITETRAD Hardware Architecture Specification (HAS)
- The Barrel Model (`docs/barrel_model/barrel_model.md`) - why four contexts
- KESTREL-RV32I MAS - the shared decode, immediate and ALU blocks

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | GATLING PRD v0.3 (`PRD.md`) | Requirements and owner decisions |
| [REF-2] | KESTREL MAS | The decode / imm_gen / ALU blocks gatling reuses |
| [REF-3] | RISC-V Instruction Set Manual, Volume I (`projects/components/riscv-ip/references/riscv-spec.pdf`) | ISA authority |
| [REF-4] | riscv-formal `rvfi.md` (`vendor/riscv-formal/docs/rvfi.md`) | RVFI retire-channel semantics |
| [REF-5] | GATLING HAS (`docs/gatling_has/`) | The external contract this MAS implements (companion) |
| [REF-6] | The Barrel Model (`docs/barrel_model/barrel_model.md`) | Why four contexts, with the kestrel-against-gatling measurement |
| [REF-7] | RISC-V Instruction Set Manual, Volume II: Privileged Architecture (same PDF as [REF-3]) | The CSRs the stub stands in for; cited as "priv §N" |
| [REF-8] | J. L. Hennessy and D. A. Patterson, *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2019 | Fine-grained multithreading, §3.11; pipeline hazards, Appendix C; the lineage from the CDC 6600 I/O processors through HEP, Tera and Niagara, Appendix M.5; cited as "H&P6 §N" |
| [REF-9] | D. A. Patterson and J. L. Hennessy, *Computer Organization and Design, RISC-V Edition*, 2nd ed., Morgan Kaufmann, 2021 | Data and control hazards, §4.8-4.9; hardware multithreading, §6.4; cited as "P&H §N" |
| [REF-10] | S. L. Harris and D. M. Harris, *Digital Design and Computer Architecture, RISC-V Edition*, Morgan Kaufmann, 2022 | Multithreading as replicated architectural state, §7.7.7; cited as "H&H §N" |
| [REF-11] | Microarchitecture reading list (`projects/components/riscv-ip/references/microarchitecture-papers.md`), entries 16-20 | The barrel's primary sources: Thornton (CDC 6600), Smith and Jordan (HEP), Alverson et al. (Tera), Kongetira et al. (Niagara); cited as "(papers, entry N)" |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| Context (hart) | One of four hardware threads: a PC, a register file, a halt state and a run bit |
| Rotation | The counter (0..NUM_HARTS-1) that names the context in F; D, X and W hold the three before it |
| Window | Four cycles: the interval between two instructions of one context |
| Context-lock | A halt that stops only its own context |
| Beat | One retired instruction on the RVFI port (tagged with its context) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-22 | seang | Initial MAS: the RV32I barrel as built (gatling_core, gatling_regfile, gatling_mem_bram); `NUM_HARTS` a parameter (default 4, at least the pipeline depth, capped at 16 by the memory system); the decode / immediate-generator / ALU blocks and ISA package shared from `riscv-ip/common-rv32i`; the CSR-stub cell; the figures (datapath, regfile and mem_bram block diagrams, the rotation grid, Waveform 4.1) and the references. Four harts on the Nexys A7. Xcell not yet built (custom-0 decodes as illegal). |

: Document Revision History

---

**Last Updated:** 2026-10-22
