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

## Bridge Micro-Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Micro-Architecture Specification |
| Version | 1.1 |
| Date | June 4, 2026 |
| Status | Released |
| Classification | Open Source - Apache 2.0 License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial release - restructured from single spec |
| 1.1 | 2026-06-04 | RTL Design Sherpa | Content sync to RTL state at 2026-06-04. Adds (1) monitor-aggregation discussion in the crossbar-core chapter — per-port `axi4_{master,slave}_{rd,wr}_mon` wrappers feed a `monbus_arbiter` tree into a single bridge-top `monbus_axil_group`, packet+timestamp carried atomically through a 192-bit skid; references the canonical 128-bit packet spec at `docs/markdown/RTLAmba/includes/monitor_package_spec.md`; (2) generator-emitted protocol-conversion shims at the slave boundary — `axi4_to_axil4_{rd,wr}` for AXIL slaves, chained with the AXIL→APB shim for APB slaves; (3) AXIL→wider-slave master-side alignment converters in the width-converters chapter (`axil_to_axi4_wide_align_{rd,wr}` — partial-word alignment, not protocol bridging); (4) generated-RTL chapter now lists monitor-variant module emission and per-port `(UNIT_ID, AGENT_ID)` assignment conventions; (5) verification-strategy chapter rewritten for protocol-BFM-only TBs with memory-backed slaves, the new `boundary_probe` test pattern, and the four `test_bridge_*_monitor_*.py` canonical patterns (smoke/capture/error_inject/irq); (6) response-routing chapter notes the independent W-tracker FIFO + split AW/W-ready MUX fix (commit `d24bd617`) that closed an interleaved-master deadlock. |

## Document Purpose

This Micro-Architecture Specification (MAS) provides detailed implementation information for the Bridge component, covering:

- Block-level architecture and internal structure
- FSM state diagrams and transition tables
- ID management and CAM architecture
- Signal-level interface details
- Width and protocol converter implementation
- Timing diagrams and debug information

For high-level architecture, system integration, and performance overview, refer to the companion **Bridge Hardware Architecture Specification (HAS)**.

## Intended Audience

- RTL designers implementing or modifying Bridge
- Verification engineers developing testbenches
- System integrators debugging Bridge behavior
- Technical staff requiring implementation details

## Related Documents

- **Bridge HAS** - Hardware Architecture Specification (high-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide
