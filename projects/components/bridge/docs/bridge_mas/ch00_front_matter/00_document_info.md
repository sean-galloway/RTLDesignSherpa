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

## Bridge Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Micro-Architecture Specification |
| Version | 1.0 |
| Date | January 3, 2026 |
| Status | Released |
| Classification | Open Source - Apache 2.0 License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial release - restructured from single spec |

## Document Purpose

This Micro-Architecture Specification (MAS) provides detailed implementation information for the Bridge component, covering:

- Block-level architecture and internal structure
- FSM state diagrams and transition tables
- ID management and CAM architecture
- Signal-level interface details
- Width and protocol converter implementation
- Timing diagrams and debug information

For high-level architecture, system integration, and performance overview, refer to the companion **Bridge Hardware Architecture Specification (HAS)**.

## Intended Audience

- RTL designers implementing or modifying Bridge
- Verification engineers developing testbenches
- System integrators debugging Bridge behavior
- Technical staff requiring implementation details

## Related Documents

- **Bridge HAS** - Hardware Architecture Specification (high-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide
