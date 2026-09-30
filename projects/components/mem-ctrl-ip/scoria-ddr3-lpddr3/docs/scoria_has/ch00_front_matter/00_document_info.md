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
| Title | scoria DDR3/LPDDR3 Family Controller — Hardware Architecture Specification |
| Version | 0.2 |
| Date | 2026-09-29 |
| Status | First edition, **pre-RTL**. Specifies the controller; does not describe an implementation |
| Scope | Controller architecture to the DFI v3.1 boundary, for DDR3 and LPDDR3 |
| Not in scope | The PHY; board bring-up; the DDR4/LPDDR4 features DFI v3.1 also carries |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| scoria design requirements | `../design-requirements.md` | **binding foundation** — the spec deltas and settled decisions |
| pumice HAS | `../../pumice-ddr2-lpddr2/docs/pumice_has/` | the architecture scoria is derived from |
| pumice design requirements | `../../pumice-ddr2-lpddr2/docs/design-requirements.md` | its coding guidelines and enforcement rules apply here unchanged |
| JESD79-3F | outside the repo, cold storage | DDR3 device standard |
| JESD209-3C | outside the repo, cold storage | LPDDR3 device standard |
| DFI v3.1 | `dfi-specs/` | the PHY boundary |

: Table 0.2: Related documents

## Terminology

**INHERITED / MODIFIED / NEW**
The marking every block in this document carries, relative to pumice.
*Inherited* means the pumice block is used as-is, and its correctness argument
transfers with it. *Modified* means a named, bounded change. *New* means no
pumice counterpart exists.

**nCK**
A DRAM clock cycle, the unit JESD79-3F states most command-spacing minimums in.

**Prime DQ bit**
In write leveling, the DQ bit (or bits) on which the DRAM returns the leveling
result.

**Maintenance traffic**
Commands the controller must issue that no host requested — refresh and ZQ
calibration. It competes with demand traffic for the command bus, which makes
it a scheduling problem and not only a sequencing one.

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 0.2 | 2026-09-29 | Q1-Q5 resolved or deferred with conditions. `refresh_ctrl` corrected from MODIFIED to INHERITED: pumice already implements `REFpb` and the device owns the sequence, so Q5 was malformed and is struck. |
| 0.1 | 2026-09-29 | First edition. Written from the delta analysis, with decisions D1-D3 settled. No RTL exists; every block is specified, not described. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 fixes purpose and vocabulary. Chapter 2 is the shape of the
controller, with one figure in which every block is colour-marked against
pumice — read that figure and you know the size of this project. Chapter 3 is
the only chapter with substantial new engineering: the four blocks DDR3 and
LPDDR3 actually change. Chapter 4 is the DFI v3.1 boundary and what moved from
v2.1.1. Chapter 5 is the package and parameters. Chapter 6 is how it will be
verified, and the questions this edition cannot answer.

**A caution particular to a pre-RTL specification.** A document written after
the fact can be incomplete; one written before can be *unbuildable*. Where this
edition states a structure, it is inherited from a controller that is built and
measured. Where it states a timing, it is cited. Where neither is true, it says
so in Chapter 6 rather than guessing.
