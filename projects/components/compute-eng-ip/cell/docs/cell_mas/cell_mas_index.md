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

# CELL Micro-Architecture Specification Index

**Component:** CELL — the compute-engine cell (one of sixteen in a tile)
**Version:** 0.14
**Date:** 2026-10-20
**Purpose:** Detailed micro-architecture specification for the cell's
slice-1 RTL as built and the slice-2/3 design decisions that complete it

---

## Overview

The **cell** is the tile's compute unit. It contains exactly one
`delta_mesh_cell` node, whose local port faces the cell's internal
datapath and whose eight mesh-facing ports pass straight through to the
cell boundary. Everything else — the RX demux, the input/result memories,
the config registers, the credit logic, the packetizer, the execution
FSM, and the ALU — is the cell's own design, speaking the tile-level
contracts of `TILE_SPEC` §11.

This book documents:

- The slice-1 modules that are already built (`cell_top`, `cell_rx`,
  `cell_cfg_regs`, `cell_mem_in`, `cell_mem_out`)
- The slice-2/3 modules that are specified here (`cell_credit`,
  `cell_packetizer`, `cell_exec_fsm`)
- The MAS decisions that close the PRD §12 open questions: memory depths,
  credit timeout, packetizer flush policy, strap initialization, and the
  execution/ALU seam
- The cycle-level behavior of the fill path as built and the expected
  behavior of the consume/emit path
- The verification plan for the credit loop and the ALU-run tests

### Key Features

- **One delta node per cell:** the node is a black box owned by
  `fabric-gen-ip/delta`; the cell consumes only its local port
- **32-line input memory, 32-line result memory:** one 32-bit line is two
  bf16 lanes; line capacity is the advertisement value today
- **Sender-generic credit returns:** per-source owed counters batch
  consumed-line credits back to the recorded source coordinate
- **Strap-gated result emission:** a `TILE_LAND_FLITS` strap counter
  (default 16) is spent per flit sent toward RAPIDS and restored by
  `credit`/`add` returns
- **Elastic ALU pipeline:** the execution FSM issues invocations into the
  ALU's valid/ready pipeline and pushes in-order results into the result
  memory

### Companion Specifications

- **[cell PRD](../PRD.md)** — the governing product definition;
  this MAS implements it
- **[TILE_SPEC §11](../../../tile/docs/TILE_SPEC.md)** — the tile's
  packet header, transport, credits, straps, and coordinate system
- **[alu-infer PRD](../../../alu-infer/PRD.md)** and
  **[alu-infer MAS](../../../alu-infer/docs/alu_infer_mas/alu_infer_mas_index.md)** —
  the normative definition of the ALU block the cell instantiates

## Design Notes

### Version History

| Version | Date | Author | Description |
|---|---|---|---|
| 0.12 | 2026-10-19 | RTL Design Sherpa | Owner rulings 2026-10-18/19: local-port width stays at delta DATA_WIDTH (64b) with beat-chained header; strap terminology replaces grants; DEST reserved, FLUSH_DEST/FLUSH_TAG operational; credit-class encoding added; gatling sequences the cell ALU. Slice-1 RTL grant identifiers noted as aliases. |
| 0.11 | 2026-10-18 | RTL Design Sherpa | Beat-chained header rule + issue-tag/same-tag-alignment MAS decision. |
| 0.10 | 2026-10-18 | RTL Design Sherpa | First cell MAS issue. Documents slice-1 RTL as built and specifies slice-2/3 modules. Closes PRD §12 open questions: IN_DEPTH=OUT_DEPTH=32 lines; CREDIT_BATCH_N default 1 with 64-cycle partial-batch timeout; EMIT_BATCH_X flush on batch-full or CTRL.flush-and-send; strap counter default 16 (mirrors TILE_LAND_FLITS). |
| 0.13 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 0.14 | 2026-10-20 | RTL Design Sherpa | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |

: Revision history

## Visual Assets

Diagram sources and renders live in `assets/graphviz/`:

- **Figure 2.1:** Whole-cell datapath —
  [`assets/graphviz/01_whole_cell.png`](assets/graphviz/01_whole_cell.png)
- **Figure 2.2:** Credit loop —
  [`assets/graphviz/02_credit_loop.png`](assets/graphviz/02_credit_loop.png)

## Navigation

Each chapter below is one source file.

#### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

#### Chapter 1: Overview

- [Design Philosophy and Scope](ch01_overview/01_overview.md)

#### Chapter 2: Functional Blocks

- [Module Tree](ch02_blocks/01_module_tree.md)
- [Datapath Figures](ch02_blocks/02_datapath_figures.md)

#### Chapter 3: Interfaces

- [External and Internal Interfaces](ch03_interfaces/01_interfaces.md)

#### Chapter 4: Micro-Architecture Behavior

- [Cycle Behavior: Fill Path as Built](ch04_behavior/01_cycle_behavior.md)
- [Credit Logic](ch04_behavior/02_credit_logic.md)
- [Packetizer and Execution FSM](ch04_behavior/03_packetizer_and_exec.md)

#### Chapter 5: Verification Hooks

- [Verification Plan](ch05_verification/01_verification_hooks.md)

#### Chapter 6: Configuration

- [Register Map and MAS Decisions](ch06_configuration/01_registers.md)

#### Chapter 7: References

- [References](ch07_references/01_references.md)

---

**Last Updated:** 2026-10-19
**Maintained By:** RTL Design Sherpa Project
