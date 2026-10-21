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

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| Context (hart) | One of four hardware threads: a PC, a register file, a halt state and a run bit |
| Rotation | The two-bit counter that names the context in F; D, X and W hold the three before it |
| Window | Four cycles: the interval between two instructions of one context |
| Context-lock | A halt that stops only its own context |
| Beat | One retired instruction on the RVFI port (tagged with its context) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-21 | seang | Initial MAS: the RV32I barrel (gatling_core, gatling_regfile, gatling_mem_bram) as built; four harts on the Nexys A7. Xcell not yet built (custom-0 decodes as illegal). |

: Document Revision History

---

**Last Updated:** 2026-10-21
