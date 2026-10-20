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

## Document Control

| Field | Value |
| --- | --- |
| Document Title | Converters Micro-Architecture Specification |
| Document Version | 1.10 |
| Component | Converters |
| Status | Active |
| Classification | Internal Technical |
| Last Updated | 2026-10-20 |

: Table 0.1: Document Control Information

## Purpose

This Micro-Architecture Specification (MAS) describes how the Converters component is actually built — the internal detail behind the feature set. It covers:

- Internal block architectures
- State machine designs
- Signal timing and handshaking
- Resource utilization estimates
- Debug and verification strategies

## Audience

This document is for:

- RTL designers implementing or modifying converter modules
- Verification engineers creating testbenches
- Integration engineers connecting converters to systems
- Performance engineers optimizing throughput and latency

## Related Documents

| Document | Purpose |
| --- | --- |
| Bridge MAS | Related crossbar micro-architecture |
| Stream MAS | Related datapath micro-architecture |

: Table 0.2: Related Documents

(The old converter spec tree was migrated into this MAS, and converters
has no standalone PRD — this book is the authoritative document.)

## Revision History

| Version | Date | Author | Description |
| --- | --- | --- | --- |
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial MAS release |
| 1.2 | 2026-09-09 | RTL Design Sherpa | Added chapter 3.10, AXI4-Lite to Wishbone B4 |
| 1.8 | 2026-10-18 | RTL Design Sherpa | 3.11: wb4_to_axil4 keeps memory order, not only termination order -- a command waits for the other direction to drain (a read behind a slow write to the same word returned old data), with a directed hazard probe. 3.15: axi4_to_axi3 stages a chopped request and checks its ID from registers, and runs the B merge from the registered BID, so neither the incoming request nor BID is in series with per-ID state (bridge W13); two directed same-ID tests. |
| 1.9 | 2026-10-18 | RTL Design Sherpa | 2.6 axi4_dwidth_converter_rd: R interleave without the beat pool. With `R_INTERLEAVE = 1` (the default, and what the bridge builds) each R beat is converted against its own ID's state as it arrives: downsize keeps a partial wide beat per ID in LUTRAM, upsize holds one wide beat and a narrow-beat count per ID. RASM_DEPTH / RASM_MAX_OUTSTANDING are unused. |
| 1.10 | 2026-10-20 | RTL Design Sherpa | Block diagrams redrawn to the repo element key (v3): class fills, double-bordered registered blocks, green return paths and a generated key under each figure. No technical content changed. |

: Table 0.3: Revision History

## Conventions

### Notation

- `signal_name` - RTL signals and parameters
- **ModuleName** - Module names and key concepts
- *Figure X.X* - Figure references

### Diagrams

Block and microarchitecture figures are graphviz, rendered to PNG:
- Source: `assets/graphviz/*.dot`
- Rendered: `assets/graphviz/*.png`

State charts, sequence charts and comparison cards are Mermaid:
- Source: `assets/mermaid/*.mmd`
- Rendered: `assets/mermaid/*.png`

### Code Examples

Treat the SystemVerilog snippets as implementation guidance: they show the intended design pattern but may differ slightly from the actual RTL.

---

**Next:** [Chapter 1: Introduction](../ch01_introduction/01_overview.md)
