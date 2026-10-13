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

## HIVE Micro-Architecture Specification

**Document Number:** HIVE-MAS-001
**Version:** 0.2
**Status:** Draft (pre-RTL — implementation intent)
**Classification:** Open Source - MIT License

---

## Document Purpose

This Micro-Architecture Specification (MAS) defines the intended internal
implementation of the HIVE subsystem at block level: the module hierarchy,
the internal interfaces between blocks, the cycle-level behavior of the key
operations, the verification hooks the RTL will expose, and the configuration
surface (parameters, defines, filelists). It is written for the RTL
implementer and for verification engineers building block-level testbenches.

The MAS assumes the external contracts of the companion HAS — packet formats,
register map, interface classes — and does not restate them except where an
internal design decision depends on the boundary detail.

**Status note:** no RTL exists yet. Everything in this document is
implementation intent to seed RTL development; where a decision is still
open, it is marked as an open item rather than resolved silently.

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | HIVE HAS v0.2 (`docs/hive_has/`) | Hardware Architecture Specification (external contract) |
| [REF-2] | HIVE PRD (`PRD.md`) | Product requirements and roadmap |
| [REF-3] | VexRiscv documentation (https://github.com/SpinalHDL/VexRiscv) | HIVE-C core generator; plugin/config reference |
| [REF-4] | SERV documentation (https://github.com/olofk/serv) | Monitor core; RF/WB interfaces |
| [REF-5] | Delta MAS (`../../../../../fabric-gen-ip/delta/docs/delta_mas/delta_mas_index.md`) | Router/NI internals HIVE configures and monitors |
| [REF-6] | Repo CDC library (`rtl/cdc/`) | Async FIFO / synchronizer building blocks for the four clock domains |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| FUB | Functional Unit Block — a leaf RTL module |
| Context memory | BRAM holding the four routing contexts per tile |
| Injection FIFO | Per-source AXIS TX buffering ahead of the Delta ingress |
| Quiesce | Drain-and-hold state a router enters before a context switch |
| Tap | Read-only observation port from a router into its SERV monitor |
| Wrapper | SV module that instantiates an external core (VexRiscv/SERV) plus glue |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-12 | seang | Initial MAS release; migrates the implementation content of the retired v0.3 `hive_specification.md` into block-level implementation intent |
| 0.2 | 2026-10-13 | seang | Owner decisions: quiesce status via fabric IDLE signal into a PeakRDL config register (hard interlock demoted to optional hardening); kestrel loader pattern; dual-flop tap synchronizers; descriptor mailbox parameter-controlled, dedicated register file default, custom-instruction alternative rejected; PKT_CONFIG injection path still TBD. Addendum: delta is the fabric (owner); everything that leaves a block is a stream — control network AXIS-shaped (32-bit, `tuser[0]` urgent), no AXI4 full in HIVE |

: Document Revision History

---

**Last Updated:** 2026-10-13
