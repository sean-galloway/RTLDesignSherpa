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
| Title | STREAM on the Genesys 2 -- The FPGA System |
| Version | 1.3 |
| Date | 2026-10-20 |
| Scope | The STREAM characterization and monitor-validation system: board, harness, the three builds, host flow |
| Not in scope | The STREAM core itself (HAS/MAS under `projects/components/dma-ip/stream/docs/`); the measured results (`reports/`, `stable/MANIFEST.md`) |
| Status | Current; written against the tree at the stream BUG-018 close (commit 022fa0e3e), run timer updated 2026-10-15 |

: Table 0.1: Document information

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition, after the component-level consolidation (one harness, one top, three parameter sets) and the mon and obs sign-off builds of September 2026. |
| 1.1 | 2026-10-15 | The run timer and CRC verdict are now `char_run_timer` from `utility-ip/misc`, shared with the RAPIDS harnesses: Figure 2.1 adds the block, Section 2 describes it, Figure 4.1's verdict names it, and the address map no longer calls `TIMER_CYCLES` free-running. |
| 1.2 | 2026-10-20 | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 1.3 | 2026-10-20 | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |

: Table 0.2: Revision history

## How to read this book

Chapter 1 is the bench. Chapter 2 is the bitstream around the DUT, block by
block, with the bridge address map every host tool depends on. Chapter 3 is
why there are three bitstreams from one source and what each is for; it is
the chapter to read before trusting a zero. Chapter 4 is the shared flow, the
per-build host layers, and the one-program-two-targets rule. Every diagram is
a Graphviz source under `assets/graphviz/`, rendered to PNG by
`regenerate_all_graphviz.sh`.
