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
| Title | RAPIDS beats on the Genesys 2 -- The AXIS4 Side |
| Version | 1.0 |
| Date | 2026-09-29 |
| Scope | The stream side of the rapids-beats characterization system: the two AXIS4 links, their stimulus and checking, their meters and observers, and what differs from STREAM's memory-to-memory harness |
| Companion | `rapids_fpga_system` (board, harness, build variants, flow) |
| Not in scope | The RAPIDS core architecture (HAS/MAS); the measured results (`reports/perf/README.md`) |
| Status | Current; written against the tree at the BUG-009 close (commit 37455c992) |

: Table 0.1: Document information

## Revision History

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-09-29 | First edition. Written after the AXIS monitor-lites (rapids TASK-015), the ingress window rework (ISSUE-001), the interleaved generator schedule (TASK-018), the 256-bit design point (report v2.0) and the ingress findings of BUG-009. |

: Table 0.2: Revision history

## How to read this book

Chapter 1 says why the rapids system is a different build from STREAM's and
what that changed in the harness. Chapter 2 is the DUT's two stream ports as
the harness sees them. Chapter 3 is the stream stimulus and checking, which
STREAM has no equivalent of. Chapter 4 is how a stream is measured: the AXIS
meters, why the ingress window is its own, and what the AXIS observers add.
Every diagram is a Graphviz source under `assets/graphviz/`.
