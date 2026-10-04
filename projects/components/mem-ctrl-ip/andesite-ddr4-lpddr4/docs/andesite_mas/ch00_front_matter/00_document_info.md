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

## andesite DDR4/LPDDR4 Family Controller Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | andesite DDR4/LPDDR4 Family Controller Micro-Architecture Specification |
| Version | 0.1 (draft) |
| Date | October 3, 2026 |
| Status | Draft — no RTL exists; expands the owner-reviewed HAS v0.1's changed and new blocks to signal level. Every claim is inherited from a named scoria source, cited to JESD79-4 / JESD209-4 / DFI 4.0 with the `§TBC(TASK-005)` discipline, or recorded as an open question in the HAS ch06 |
| Classification | Open Source - MIT License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-03 | RTL Design Sherpa | First draft, written before any RTL exists. Carries the HAS's changed/new blocks one level down: per-block interface tables, FSM policy, mechanism detail, and the contract anchors the generated kmap book cites. Inherited-unchanged blocks are referenced to scoria's books, not rewritten. |

## Document Purpose

This Micro-Architecture Specification (MAS) is the implementation-level view
of the andesite controller — the HAS (`../andesite_has/`) taken one level
down. It is the document an RTL author reads before writing SystemVerilog and
a verification engineer reads before writing checkers.

It covers:

- each changed or new block's interface, parameters, and internal mechanism
- the FSM policy for every block: where a state machine is required, where
  one is forbidden (no training search loops, per the D2 precedent), and what
  replaces FSMs elsewhere
- the DFI 4.0 pin-level table the HAS's interface chapter promises
- the core signal contracts whose anchors the generated kmap book
  (`../kmaps/`) verifies by citation

## Intended Audience

- RTL implementers writing the changed and new blocks
- Verification engineers building the DFI 4.0 BFM checks and the formal
  spacing properties the HAS ch06 names
- Architects confirming that a block-level decision matches the HAS's
  marking and cause

## Related Documents

| Document | Location | Content |
|---|---|---|
| Hardware Architecture Specification | `../andesite_has/andesite_has_index.md` | the owner-reviewed v0.1 architecture this document expands; bindings between the two follow the HAS |
| Bootstrap design spec | `../../../../../../docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md` | the tranche's scope decisions (§6 is this book's plan) |
| Family docs | `../../../../docs/` | shared-core design (`mem_ctrl_pkg`) and family doctrine |
| scoria HAS | `../../../scoria-ddr3-lpddr3/docs/scoria_has/` | the reuse pool; authoritative for inherited-unchanged blocks |
| scoria design requirements | `../../../scoria-ddr3-lpddr3/docs/design-requirements.md` | the delta-analysis method; TASK-001 mode detail (§6) |
| Kmap generator + workbook | `../kmaps/` | generated command-encoding tables citing this book's anchors |
| CLAUDE.md | `../../../andesite-ddr4-lpddr4/CLAUDE.md` | area facts for a session working here |

: Table 0.1: Related documents
