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

| Field | Value |
|-------|-------|
| Title | andesite DDR4/LPDDR4 Family Controller — Hardware Architecture Specification |
| Version | 0.1 |
| Date | 2026-10-03 |
| Status | First edition, written from the delta analysis against scoria before any andesite RTL exists. Every block is specified, not described; open questions are collected in Chapter 6 |
| Scope | Controller architecture to the DFI v4.0 boundary, for DDR4 and LPDDR4 |
| Not in scope | The PHY; board bring-up; the DDR5 features DFI v4.x also carries |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| andesite bootstrap design spec | `../../../../../../docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md` | **binding foundation** — the scope decisions and settled filing |
| scoria HAS | `../../../scoria-ddr3-lpddr3/docs/scoria_has/` | the architecture andesite is derived from; the reuse pool |
| scoria design requirements | `../../../scoria-ddr3-lpddr3/docs/design-requirements.md` | its delta-analysis method and D1-D3 decisions apply here |
| family docs | `../../../../docs/` | shared-core design and doctrine — owned by no single controller (see Table 0.1 note) |
| JESD79-4 | outside the repo, cold storage | DDR4 device standard |
| JESD209-4 | outside the repo, cold storage | LPDDR4 device standard |
| DFI v4.0 | operator research storage `/mnt/data/github/dfi-specs/` (on disk 2026-10-04); study is andesite TASK-005 | the PHY boundary; clause citations carry `§TBC(TASK-005)` until the study confirms them |

: Table 0.2: Related documents

## Terminology

**INHERITED / MODIFIED / NEW**
The marking every block in this document carries, relative to scoria.
*Inherited* means the scoria block is used as-is, and its correctness argument
transfers with it. *Modified* means a named, bounded change. *New* means no
scoria counterpart exists.

**nCK**
A DRAM clock cycle, the unit JESD79-4 states most command-spacing minimums in.

**Maintenance traffic**
Commands the controller must issue that no host requested — refresh and ZQ
calibration. It competes with demand traffic for the command bus, which makes
it a scheduling problem and not only a sequencing one.

**DFI 4.0 §TBC(TASK-005)**
Read "clause to be confirmed by andesite TASK-005 (DFI 4.0 spec acquisition
and BFM study)". The suffix marks a claim whose substance is asserted but
whose clause number cannot be verified in-house because the specification is
not on disk.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 0.1 | 2026-10-03 | First edition, from the 2026-10-03 bootstrap spec. Written before RTL, the way scoria's 0.1 was: the delta analysis settles the markings, the design point, and the DFI 4.0 boundary; the MAS and the kmap book follow as separate books. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 fixes purpose and vocabulary. Chapter 2 is the shape of the
controller, with one figure in which every block is colour-marked against
scoria — read that figure and you know the size of this project. Chapter 3 is
the heart: the ten areas DDR4 and LPDDR4 actually change, and the dormant and
deferred lists. Chapter 4 is the DFI v4.0 boundary and what moved from v3.1.
Chapter 5 is the package and parameters. Chapter 6 is how it is verified, and
what separates this edition from a 1.0.

**The caution this document carries by construction.** v0.1 is written before
the RTL, and a specification written first can be *unbuildable* — that is the
risk it carries. The evidentiary rule is the mitigation, and it is stricter
than scoria's in one place: no DFI 4.0 spec exists on disk, so DFI 4.0 clause
numbers are `§TBC(TASK-005)` throughout rather than cited. Where
implementation later corrects the specification, the correction belongs in
this revision history, not dropped silently.
