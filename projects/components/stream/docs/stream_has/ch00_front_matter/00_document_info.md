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

## STREAM Hardware Architecture Specification

**Document Number:** STREAM-HAS-001
**Version:** 0.92
**Status:** Draft
**Classification:** Open Source - Apache 2.0 License

---

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level architectural overview of the STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory) subsystem. It describes the system-level design, external interfaces, performance characteristics, and integration requirements without detailing internal implementation specifics.

**Target Audience:**
- System architects evaluating STREAM for integration
- Hardware engineers planning system-level integration
- Software engineers developing drivers and firmware
- Verification engineers planning system-level testing

**Companion Documents:**
- STREAM Micro-Architecture Specification (MAS) - Detailed block-level implementation
- STREAM Product Requirements Document (PRD) - Requirements and rationale

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | STREAM MAS v0.90 | Micro-Architecture Specification |
| [REF-2] | STREAM PRD | Product Requirements Document |
| [REF-3] | ARM AMBA AXI4 | AXI4 Protocol Specification |
| [REF-4] | ARM AMBA APB | APB Protocol Specification |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| AXI | Advanced eXtensible Interface - ARM AMBA high-performance bus |
| APB | Advanced Peripheral Bus - ARM AMBA low-power configuration bus |
| Beat | Single data transfer on AXI bus (one clock cycle of valid data) |
| Burst | Sequence of consecutive beats forming a single AXI transaction |
| Channel | Independent DMA transfer context (STREAM supports 8 channels) |
| Descriptor | 256-bit data structure defining a single DMA transfer operation |
| DMA | Direct Memory Access - data transfer without CPU involvement |
| HAS | Hardware Architecture Specification |
| MAS | Micro-Architecture Specification |
| MonBus | Monitor Bus - internal debug/trace event streaming interface |
| Scatter-Gather | DMA mode using linked descriptors for non-contiguous transfers |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.90 | 2026-01-03 | seang | Initial HAS release |
| 0.91 | 2026-05-14 | seang | Sync to RTL changes since 2026-04-17 (commit `be4e5a91`); regenerate PDFs/DOCX. |
| 0.92 | 2026-06-05 | seang | Sync to RTL state at 2026-06-05 (17 commits since `be4e5a91`). Documents (1) the 64→128-bit monbus packet migration + new 64-bit side-band timestamp wire — referenced via `docs/markdown/RTLAmba/includes/monitor_package_spec.md`, with `cfg_ts_append_*` removed and m_axil records locked to 3 beats; (2) new APB channel-observation register set (`OBS_CTRL` / `OBS_FLAGS` / `OBS_DATA0` / `OBS_DATA1`) that exposes scheduler error stickies + timeout per channel; (3) BOTH-end descriptor-path monitoring with distinct `(UNIT_ID, AGENT_ID)` for fetch-side vs. consume-side, under the new per-port + global SV-parameter monitor methodology; (4) three RTL fixes — drain-ctrl stale-view race + post-flop wvalid gate (`a82627af`), registered `w_arb_request` for 8-channel timing closure (`4e8f9e02`), reset on SRAM avail outputs (`b619eee9`); (5) `stream_core_mon` duplicate cleanup (`7291c4ef`). |

: Document Revision History

---

**Last Updated:** 2026-06-05
