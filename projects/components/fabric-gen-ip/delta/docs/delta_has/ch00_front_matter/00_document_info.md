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

## Delta Hardware Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Delta Hardware Architecture Specification |
| Version | 1.2 |
| Date | 2026-10-20 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document Properties

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial HAS/MAS split; documents the 2026-10-12 richness options (TSTRB and AMBA5 TWAKEUP/TPARITY) and flat-only topology. |
| 1.1 | 2026-10-12 | RTL Design Sherpa | AMBA 5 interface parity per IHI 0051B ch. 5 (issue #102): `TPARITY`/`PW_WIDTH`/`--parity-width` replaced by the odd-parity check signals `TDATACHK` ... `TWAKEUPCHK` (spec widths, checked at every port, sticky `*_parity_error`), matching `rtl/amba/axis5`. First `dv/` suite. |
| 1.2 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |

: Revision History

## Document Purpose

This Hardware Architecture Specification (HAS) is the high-level view of the Delta AXI4-Stream crossbar generator — the map you read before you integrate, not the schematic. It covers:

- System-level architecture and data flow
- AXI4-Stream protocol support (base and rich flavors)
- Interface definitions and requirements
- Performance characteristics
- Integration guidelines

For micro-architecture, FSM designs, and signal-level detail, see the companion **Delta Micro-Architecture Specification (MAS)**.

## Intended Audience

- System architects defining streaming interconnect topology
- Hardware engineers integrating Delta into SoC designs
- Verification engineers planning test strategies
- Technical managers evaluating Delta capabilities

## Related Documents

- **Delta MAS** - Micro-Architecture Specification (detailed block-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI assistant integration guide
- **QUICK_START.md** - Hands-on generator guide
