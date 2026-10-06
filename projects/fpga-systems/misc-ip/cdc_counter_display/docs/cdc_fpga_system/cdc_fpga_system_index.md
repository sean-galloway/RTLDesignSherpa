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

# CDC Counter Display on the Nexys A7 -- The FPGA System

**Version:** 1.0
**Date:** 2026-09-29
**Purpose:** What is on the bench and in the bitstream for the CDC
demonstration: the board, the two builds and how far apart they really are, the
harness around the four counter domains, the five selectable crossings, and the
flow that makes an unsafe crossing fail visibly on demand.

> The operator procedure lives in `docs/cdc_demo_guide/` and `docs/HARNESS.md`,
> and the taxonomy of CDC failure modes in `docs/CDC_DEMO_TODO.md`. This book
> explains the apparatus: what is in each bitstream, why the two builds share
> almost nothing, and why each part of the demonstration is shaped the way it is.

---

## Quick reference

| Question | Answer | Chapter |
|---|---|---|
| Which build is the default? | `build-demo`; `BUILD=phase1` selects the other | 1, 3 |
| Is the harness RTL different per build? | Yes, completely -- `build-phase1` has no harness at all | 3 |
| How many counters, and why? | Four: one under test and three as a control group | 1, 4 |
| Which mode is the broken one? | Mode 0, `NO_CDC`: raw flop per bit, no Gray, no `ASYNC_REG` | 2 |
| Why sweep the clock instead of just setting mode 0? | Mode 0 mostly works when slow; the sweep is what makes the failure appear | 4 |
| How do I know the counter is fine and the crossing is not? | `PRESS_COUNT` crosses Gray-coded and stays correct while `VALUE` does not | 2, 4 |
| Build ID? | `0x43434331`, ASCII `CDC1` | 2 |

: Table 0.0: Quick reference

---

## Document Organization

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: The System
- [The Board, and the Build That Needs No Host](ch01_overview/01_system.md)

### Chapter 2: The Harness
- [The Registers, the Four Counter Domains, the Clock Tree and the Five Crossings](ch02_harness/01_harness.md)

### Chapter 3: Two Builds, Two Designs
- [Why the Harness RTL Differs Here and Not in the pumice System](ch03_builds/01_build_variants.md)

### Chapter 4: Host Tools and Flow
- [watch-fail, and Why Every Step of It Is Necessary](ch04_host_and_flow/01_host_and_flow.md)

---

## Diagrams

Every figure is a Graphviz source in `assets/graphviz/`, rendered to PNG by
`assets/graphviz/regenerate_all_graphviz.sh`. Edit the `.dot` and re-run the
script; never hand-edit a PNG.

| Figure | Source | Subject |
|---|---|---|
| 1.1 | `01_board_and_host.dot` | the board, and the host only one build needs |
| 2.1 | `02_harness_blocks.dot` | the CSR block, four counter domains, the clock tree, five crossings |
| 3.1 | `03_build_variants.dot` | two builds, two disjoint designs, one dispatcher |
| 4.1 | `04_measurement_path.dot` | the watch-fail sequence and why each step is there |

: Table 0.1: The diagrams and their sources
