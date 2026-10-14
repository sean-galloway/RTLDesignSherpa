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

## Lattice Generator Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Lattice Generator Architecture Specification |
| Version | 1.0 |
| Date | 2026-10-12 |
| Status | Released |
| Classification | Open Source - MIT License |

: Document Properties

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-10-12 | RTL Design Sherpa | Initial GAS release — verified against `apbx_xbar_generator.py`, `generate_xbars.py`, and emitted fixtures in `rtl/`. |
| 1.2 | 2026-10-13 | seang | Rebrand: component codename **lattice**, directory `lattice-apbx-xbar`; book titles and document number (LATTICE-GAS-001) updated; RTL module names unchanged (`apbx_xbar_*`) |

: Document Revision History

## Document Purpose

This Generator Architecture Specification (GAS) documents the Lattice code generator. It is written for the engineer who must re-run the generator, add a new variant or option, or understand why a generated module looks the way it does.

For the generated hardware, see the **Lattice HAS** and **MAS**. For product requirements, see **PRD.md**.

## Intended Audience

- RTL engineers extending the generator
- Verification engineers regenerating fixtures
- Integrators choosing pre-generated vs custom variants

## Related Documents

- **Lattice HAS** - Hardware Architecture Specification
- **Lattice MAS** - Micro-Architecture Specification
- **PRD.md** - Product requirements
- **CLAUDE.md** - AI development guide
