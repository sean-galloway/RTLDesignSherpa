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
| Title | RAPIDS beats on the Genesys 2 -- The FPGA System |
| Version | 1.0 |
| Date | 2026-09-29 |
| Scope | The `rapids_beats` characterization system: board, harness, build variants, host flow |
| Not in scope | The RAPIDS core itself (HAS/MAS under `projects/components/dma-ip/rapids/docs/`); the measured numbers (`reports/perf/README.md`) |
| Status | Current; written against the tree at the BUG-009 close (commit 37455c992) |

: Table 0.1: Document information

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition. Written after the 256-bit / 4 KB design point (report v2.0) and the BUG-009 close (report v2.2), so it describes the observers, monitors-in, 16 KB and ILA variants as actually built this month. |

: Table 0.2: Revision history

## How to read this book

Chapter 1 is the bench: what is plugged into what. Chapter 2 is the bitstream
around the DUT, block by block, and the launch path a measurement takes.
Chapter 3 is the reason there is more than one bitstream, and what each one
buys. Chapter 4 is the flow: make targets, the host tools, and how a JSON row
becomes a report cell. Every diagram is a Graphviz source under
`assets/graphviz/`, rendered to PNG by `regenerate_all_graphviz.sh`.
