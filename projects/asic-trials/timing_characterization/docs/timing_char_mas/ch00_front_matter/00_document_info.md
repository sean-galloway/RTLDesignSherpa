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

## Timing Characterization Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Timing Characterization Micro-Architecture Specification |
| Version | 1.0 |
| Date | March 18, 2026 |
| Status | Released |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-03-18 | RTL Design Sherpa | Initial release |

## Document Purpose

This document provides the detailed micro-architecture specification for the
Timing Characterization component. It covers the implementation of each
Functional Unit Block (FUB), the shared LFSR engine, anti-optimization
techniques, and verification infrastructure.

For the high-level system architecture, refer to the companion Hardware
Architecture Specification (HAS).

## Intended Audience

- Hardware engineers implementing or extending the characterization harness
- Verification engineers writing tests for new FUBs
- Synthesis engineers setting up characterization flows
- AI assistants working on this component

## Related Documents

| Document | Description |
|----------|-------------|
| **Timing Characterization HAS** | Hardware architecture specification (system-level) |
| **PRD.md** | Product requirements document |
| **CLAUDE.md** | AI development guide |
| **SYNTHESIS_GUIDE.md** | Detailed synthesis workflow and result interpretation |
