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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Document Information

## Overview

### CELL Micro-Architecture Specification

| Property | Value |
|---|---|
| Document Title | CELL Micro-Architecture Specification |
| Version | 0.14 |
| Date | 2026-10-20 |
| Status | Draft — slice-1 RTL built; slice-2/3 modules specified |
| Classification | Open Source - MIT License |

: Document information

### Document Purpose

This Micro-Architecture Specification (MAS) documents how the compute cell
is built and how the remaining slice-2/3 work completes it:

- The slice-1 module tree (`cell_top`, `cell_rx`, `cell_cfg_regs`,
  `cell_mem_in`, `cell_mem_out`) as it exists today
- The slice-2/3 modules (`cell_credit`, `cell_packetizer`, `cell_exec_fsm`)
  that are specified here
- The MAS decisions that close the PRD §12 open questions
- The cycle-level behavior of the fill path as built and the expected
  consume/emit path
- The verification plan for the credit loop and ALU-run tests

For what the cell must do and why, see the **cell PRD** (normative for
the cell product). For the packet, credit, and coordinate protocols the
cell consumes, see **TILE_SPEC §11**. For the ALU block itself, see the
**alu-infer PRD** and **alu-infer MAS**.

### Intended Audience

- RTL designers implementing the slice-2/3 modules inside `cell/rtl/`
- Verification engineers extending `cell/dv/tests/test_cell.py`
- Design reviewers checking the future implementation against intent
- Students reading the cell datapath top to bottom

## Design Notes

### Revision History

| Version | Date | Author | Description |
|---|---|---|---|
| 0.11 | 2026-10-18 | RTL Design Sherpa | Beat-chained header rule (owner ruling): the 128-bit tile header occupies the first `ceil(128/DW)` payload beats, LSB-first; every link keeps its own width. Local port stays at delta `DATA_WIDTH` (64b) — supersedes 0.10's 128-bit local-port widening. TILE_SPEC v1.6+ binding. |
| 0.12 | 2026-10-19 | RTL Design Sherpa | (addendum) Owner rulings 2026-10-18/19: local-port width stays at delta DATA_WIDTH (64b) with beat-chained header; strap terminology replaces grants in registers/PRD; DEST reserved, FLUSH_DEST/FLUSH_TAG are the operational drain destination; credit-class encoding added; gatling sequences the cell ALU. Slice-1 RTL identifiers retain pre-ruling grant names (noted in ch06). |
| 0.11 | 2026-10-18 | RTL Design Sherpa | (same-day addendum) ALU-focus datapath figure (fig 2.3, no delta side) + issue-tag / same-tag-alignment MAS decision in ch04 §4.4 — ratified owner ruling; tag assign/FIFO/align gate not yet in alu-infer RTL. |
| 0.10 | 2026-10-18 | RTL Design Sherpa | First issue. Slice-1 RTL built; slice-2/3 specified. Closes PRD §12 open questions with MAS decisions: IN_DEPTH=OUT_DEPTH=32 lines; CREDIT_BATCH_N default 1; 64-cycle partial-batch credit timeout; EMIT_BATCH_X flush on batch-full or CTRL.flush-and-send; strap counter default 16; local-port data width widens to 128 bits to carry the §11.6 tile header. |

: Revision history

## References

### Related Documents

- **cell PRD** ([../../../PRD.md](../../PRD.md)) — product definition,
  normative for the cell
- **TILE_SPEC §11**
  ([../../../../tile/docs/TILE_SPEC.md](../../../../tile/docs/TILE_SPEC.md)) —
  packet header, transport, credits/grants, coordinates
- **alu-infer PRD** ([../../../../alu-infer/PRD.md](../../../../alu-infer/PRD.md)) —
  normative definition of the ALU block
- **alu-infer MAS**
  ([../../../../alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md](../../../../alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md)) —
  implementation-intent book for the ALU block
- **delta_mesh_cell**
  ([../../../../../fabric-gen-ip/delta/rtl/delta_mesh_cell.sv](../../../../../fabric-gen-ip/delta/rtl/delta_mesh_cell.sv)) —
  the node the cell instantiates

---

**Last Updated:** 2026-10-19
