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

## STREAM Hardware Architecture Specification

**Document Number:** STREAM-HAS-001
**Version:** 0.90
**Status:** Draft
**Classification:** Open Source - Apache 2.0 License

---

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level architectural overview of the STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory) subsystem. It describes the system-level design, external interfaces, performance characteristics, and integration requirements without detailing internal implementation specifics.

**Target Audience:**
- System architects evaluating STREAM for integration
- Hardware engineers planning system-level integration
- Software engineers developing drivers and firmware
- Verification engineers planning system-level testing

**Companion Documents:**
- STREAM Micro-Architecture Specification (MAS) - Detailed block-level implementation
- STREAM Product Requirements Document (PRD) - Requirements and rationale

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | STREAM MAS v0.90 | Micro-Architecture Specification |
| [REF-2] | STREAM PRD | Product Requirements Document |
| [REF-3] | ARM AMBA AXI4 | AXI4 Protocol Specification |
| [REF-4] | ARM AMBA APB | APB Protocol Specification |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| AXI | Advanced eXtensible Interface - ARM AMBA high-performance bus |
| APB | Advanced Peripheral Bus - ARM AMBA low-power configuration bus |
| Beat | Single data transfer on AXI bus (one clock cycle of valid data) |
| Burst | Sequence of consecutive beats forming a single AXI transaction |
| Channel | Independent DMA transfer context (STREAM supports 8 channels) |
| Descriptor | 256-bit data structure defining a single DMA transfer operation |
| DMA | Direct Memory Access - data transfer without CPU involvement |
| HAS | Hardware Architecture Specification |
| MAS | Micro-Architecture Specification |
| MonBus | Monitor Bus - internal debug/trace event streaming interface |
| Scatter-Gather | DMA mode using linked descriptors for non-contiguous transfers |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.90 | 2026-01-03 | seang | Initial HAS release |

: Document Revision History

---

**Last Updated:** 2026-01-03
