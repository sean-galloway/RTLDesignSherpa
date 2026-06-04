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

## Bridge Hardware Architecture Specification

| Property | Value |
|----------|-------|
| Document Title | Bridge Hardware Architecture Specification |
| Version | 1.1 |
| Date | June 4, 2026 |
| Status | Released |
| Classification | Open Source - Apache 2.0 License |

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2026-01-03 | RTL Design Sherpa | Initial release - restructured from single spec |
| 1.1 | 2026-06-04 | RTL Design Sherpa | Content sync to RTL state at 2026-06-04. Documents (1) the 64→128-bit monbus packet migration with new 64-bit side-band timestamp wire — referenced via `docs/markdown/RTLAmba/includes/monitor_package_spec.md`; (2) per-port + global SV-parameter monitor methodology with mandatory `use_monitor` TOML field and `variants = ["no","mon"]` generator selector; (3) generator-emitted AXI4↔AXIL conversion at the slave boundary (was external); (4) new AXIL→wider-slave master-side alignment converters (`axil_to_axi4_wide_align_{rd,wr}`); (5) verification-strategy rewrite to protocol-BFM-only TBs with memory-backed slaves, serial-only execution, per-module cocotb function names, boundary_probe (renamed from address_decode) tests; (6) note of the independent W-tracker FIFO + split AW/W-ready MUX fix (commit `d24bd617`) that closed an interleaved-master deadlock. |

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level view of the Bridge component, covering:

- System-level architecture and data flow
- Protocol support (AXI4, AXI4-Lite, APB)
- Interface definitions and requirements
- Performance characteristics
- Integration guidelines

For detailed micro-architecture, FSM designs, and signal-level specifications, refer to the companion **Bridge Micro-Architecture Specification (MAS)**.

## Intended Audience

- System architects defining interconnect topology
- Hardware engineers integrating Bridge into SoC designs
- Verification engineers planning test strategies
- Technical managers evaluating Bridge capabilities

## Related Documents

- **Bridge MAS** - Micro-Architecture Specification (detailed block-level)
- **PRD.md** - Product requirements and overview
- **CLAUDE.md** - AI development guide
