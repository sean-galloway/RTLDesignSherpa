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
| Version | 1.4 |
| Date | 2026-10-24 |
| Scope | The STREAM characterization and monitor-validation system: board, harness, the builds (mon, obs, perf and perf with stream-g), host flow, and the board-side STREAM / stream-g comparison |
| Not in scope | The STREAM core itself and the choice between STREAM and stream-g (HAS/MAS under `projects/components/dma-ip/stream/docs/`); the monitor and extended-addressing results (`reports/`, `stable/MANIFEST.md`) |
| Status | Current; written against the tree at the stream BUG-018 close (commit 022fa0e3e), run timer updated 2026-10-15 |

: Table 0.1: Document information

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition, after the component-level consolidation (one harness, one top, three parameter sets) and the mon and obs sign-off builds of September 2026. |
| 1.1 | 2026-10-15 | The run timer and CRC verdict are now `char_run_timer` from `utility-ip/misc`, shared with the RAPIDS harnesses: Figure 2.1 adds the block, Section 2 describes it, Figure 4.1's verdict names it, and the address map no longer calls `TIMER_CYCLES` free-running. |
| 1.2 | 2026-10-20 | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |
| 1.3 | 2026-10-20 | Section (h2) headings now open a new page, the pipeline default. No technical content changed. |
| 1.4 | 2026-10-24 | Chapter 5, STREAM against stream-g on this board (stream TASK-020): the `STREAM_G` / `FW_WRITABLE` build, Figure 5.1 (the stream-g DUT's register path and sequencing in the harness), the two bitstreams' area and timing, the A/B method (Figure 5.2: one tree, one host program, the gcompare / gscale / gscale1 point profiles on the board and in simulation), every measured table, the first dead stream-g bitstream and the undriven-net scan it added to `make bitstream`, and the ILA build. Chapter 3 gains the stream-g build row and the `STREAM_G`, `FW_WRITABLE`, `STREAM_CHAR_ILA`, `STREAM_SHARED_ENGINES` and clock knobs; Figures 2.1 and 3.1 name the second DUT. |

: Table 0.2: Revision history

## How to read this book

Chapter 1 is the bench. Chapter 2 is the bitstream around the DUT, block by
block, with the bridge address map every host tool depends on. Chapter 3 is
why there are three bitstreams from one source and what each is for; it is
the chapter to read before trusting a zero. Chapter 4 is the shared flow, the
per-build host layers, and the one-program-two-targets rule. Chapter 5 is
STREAM against stream-g on this board: the build, the method and the numbers. Every diagram is
a Graphviz source under `assets/graphviz/`, rendered to PNG by
`regenerate_all_graphviz.sh`.
