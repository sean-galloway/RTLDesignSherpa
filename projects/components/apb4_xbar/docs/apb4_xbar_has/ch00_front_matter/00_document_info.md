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

## APB Crossbar Hardware Architecture Specification

**Document Number:** APB-XBAR-HAS-001
**Version:** 1.0
**Status:** Production Ready
**Classification:** Open Source - Apache 2.0 License

---

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level architectural overview of the APB Crossbar component. It describes the system-level design, external interfaces, performance characteristics, and integration requirements without detailing internal implementation specifics.

**Target Audience:**
- System architects evaluating APB Crossbar for SoC integration
- Hardware engineers planning peripheral interconnect design
- Software engineers developing drivers and firmware
- Verification engineers planning system-level testing

**Companion Documents:**
- APB Crossbar Micro-Architecture Specification (MAS) - Detailed block-level implementation
- APB Crossbar Product Requirements Document (PRD) - Requirements and rationale

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | APB Crossbar MAS v1.0 | Micro-Architecture Specification |
| [REF-2] | APB Crossbar PRD | Product Requirements Document |
| [REF-3] | ARM AMBA APB | APB Protocol Specification (IHI 0024C) |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| APB | Advanced Peripheral Bus - ARM AMBA low-power peripheral bus |
| Arbiter | Logic that selects between competing requests using round-robin |
| Crossbar | NxM interconnect fabric connecting multiple masters to multiple slaves |
| Master | APB initiator device that initiates read/write transactions |
| PSEL | APB peripheral select signal indicating slave selection |
| PENABLE | APB enable signal indicating data phase of transaction |
| PREADY | APB ready signal indicating slave response completion |
| Slave | APB target device that responds to master transactions |
| Transaction | Complete APB read or write operation (setup + data phase) |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | seang | Initial HAS release |

: Document Revision History

---

**Last Updated:** 2026-01-03
