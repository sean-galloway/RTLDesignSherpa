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

This Micro-Architecture Specification (MAS) describes how the Converters component is implemented — the internal detail behind the feature set. It covers:

- Internal block architectures
- State machine designs
- Signal timing and handshaking
- Resource utilization estimates
- Debug and verification strategies

## Audience

This document is for:

- RTL designers implementing or modifying converter modules
- Verification engineers creating testbenches
- Integration engineers connecting converters to systems
- Performance engineers optimizing throughput and latency

## Related Documents

| Document | Purpose |
|----------|---------|
| Bridge MAS | Related crossbar micro-architecture |
| Stream MAS | Related datapath micro-architecture |

: Table 0.2: Related Documents

(The old converter spec tree was migrated into this MAS, and converters
has no standalone PRD — this book is the authoritative document.)

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

The SystemVerilog snippets are implementation guidance: they show the intended design pattern but may differ slightly from the actual RTL.

---

**Next:** [Chapter 1: Introduction](../ch01_introduction/01_overview.md)
