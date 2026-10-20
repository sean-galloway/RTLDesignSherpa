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

## Delta Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Delta Micro-Architecture Specification |
| Version | 1.3 |
| Date | 2026-10-20 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document Properties

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial release; describes the generated flat crossbar RTL including request decode, packet-atomic RR arbitration, mux, TREADY/TWAKEUP steering, counters, and assertions. |
| 1.1 | 2026-10-12 | RTL Design Sherpa | AMBA 5 interface parity per IHI 0051B ch. 5 (issue #102): `TPARITY`/`PW_WIDTH`/`--parity-width` replaced by the odd-parity check signals `TDATACHK` ... `TWAKEUPCHK` (spec widths, checked at every port, sticky `*_parity_error`), matching `rtl/amba/axis5`. First `dv/` suite. |
| 1.2 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 1.3 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |

: Revision History

## Document Purpose

This Micro-Architecture Specification (MAS) is the internals document for the Delta AXI4-Stream crossbar generator — the one you open when you need to know what the generated RTL actually does, block by block. It covers:

- Block-level implementation of the generated SystemVerilog
- Arbitration state behavior and grant hold/release rules
- Cycle-level behavior examples
- Parameter-to-logic implications
- Verification strategy

For the high-level architecture, interface requirements, and integration guidelines, see the companion **Delta Hardware Architecture Specification (HAS)**.

## Intended Audience

- RTL engineers reading or modifying the generated crossbar
- Verification engineers writing protocol checks
- System architects resolving timing or arbitration questions
- Technical reviewers auditing the implementation

## Related Documents

- **Delta HAS** - Hardware Architecture Specification (high-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI assistant integration guide
- **QUICK_START.md** - Hands-on generator guide
