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

## Document Control

| Field | Value |
|-------|-------|
| Document Title | Converters Micro-Architecture Specification |
| Document Version | 1.0 |
| Component | Converters |
| Status | Active |
| Classification | Internal Technical |
| Last Updated | 2026-01-03 |

: Table 0.1: Document Control Information

## Purpose

This Micro-Architecture Specification (MAS) provides detailed implementation guidance for the Converters component. It covers:

- Internal block architectures
- State machine designs
- Signal timing and handshaking
- Resource utilization estimates
- Debug and verification strategies

## Audience

This document is intended for:

- RTL designers implementing or modifying converter modules
- Verification engineers creating testbenches
- Integration engineers connecting converters to systems
- Performance engineers optimizing throughput and latency

## Related Documents

| Document | Purpose |
|----------|---------|
| Converters Spec | High-level feature specification |
| Component PRD | Product requirements and goals |
| Bridge MAS | Related crossbar micro-architecture |
| Stream MAS | Related datapath micro-architecture |

: Table 0.2: Related Documents

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial MAS release |

: Table 0.3: Revision History

## Conventions

### Notation

- `signal_name` - RTL signals and parameters
- **ModuleName** - Module names and key concepts
- *Figure X.X* - Figure references

### Diagrams

All diagrams use Mermaid format rendered to PNG:
- Source: `assets/mermaid/*.mmd`
- Rendered: `assets/mermaid/*.png`

### Code Examples

SystemVerilog code snippets are provided for implementation guidance. These represent the intended design pattern but may differ slightly from actual RTL.

---

**Next:** [Chapter 1: Introduction](../ch01_introduction/01_overview.md)
