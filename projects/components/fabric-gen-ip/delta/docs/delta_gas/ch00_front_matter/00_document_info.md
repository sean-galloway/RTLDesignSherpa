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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Document Information

## Delta Generator Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Delta Generator Architecture Specification |
| Version | 1.2 |
| Date | 2026-10-20 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document Properties

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial GAS release — verified against `delta_generator.py`, `complete_tree_generator.py`, and emitted fixtures in `rtl/`. |
| 1.1 | 2026-10-12 | RTL Design Sherpa | AMBA 5 interface parity per IHI 0051B ch. 5 (issue #102): `TPARITY`/`PW_WIDTH`/`--parity-width` replaced by the odd-parity check signals `TDATACHK` ... `TWAKEUPCHK` (spec widths, checked at every port, sticky `*_parity_error`), matching `rtl/amba/axis5`. First `dv/` suite. |
| 1.2 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |

: Revision History

## Document Purpose

This Generator Architecture Specification (GAS) documents the Delta AXI-Stream crossbar code generator. It is written for the engineer who must re-run the generator, add a new topology or option, or understand why a generated module looks the way it does.

For the generated hardware, see the **Delta HAS** and **MAS**. For product requirements, see **PRD.md**.

## Intended Audience

- RTL engineers extending the generator
- Verification engineers regenerating fixtures
- Integrators choosing pre-generated vs custom variants

## Related Documents

- **Delta HAS** - Hardware Architecture Specification
- **Delta MAS** - Micro-Architecture Specification
- **PRD.md** - Product requirements
- **CLAUDE.md** - AI development guide
