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
**Version:** 0.95
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
| 0.92 | 2026-06-05 | seang | Sync to RTL state at 2026-06-05 (17 commits since `be4e5a91`). Documents (1) the 64→128-bit monbus packet migration + new 64-bit side-band timestamp wire — referenced via `docs/markdown/rtl-amba/includes/monitor_package_spec.md`, with `cfg_ts_append_*` removed and m_axil records locked to 3 beats; (2) new APB channel-observation register set (`OBS_CTRL` / `OBS_FLAGS` / `OBS_DATA0` / `OBS_DATA1`) that exposes scheduler error stickies + timeout per channel; (3) BOTH-end descriptor-path monitoring with distinct `(UNIT_ID, AGENT_ID)` for fetch-side vs. consume-side, under the new per-port + global SV-parameter monitor methodology; (4) three RTL fixes — drain-ctrl stale-view race + post-flop wvalid gate (`a82627af`), registered `w_arb_request` for 8-channel timing closure (`4e8f9e02`), reset on SRAM avail outputs (`b619eee9`); (5) `stream_core_mon` duplicate cleanup (`7291c4ef`). |
| 0.93 | 2026-07-02 | seang | Monitor registers relocated to a separate `stream_mon_regs` regfile at 0x1000 (single APB slave); APB address decode widened to 13 bits / 8 KB so the monitor block is addressable (`ch04_interfaces/02_apb4_slave.md`). Companion MAS documents `SCHED_TIMEOUT_LIMIT` + the recoverable scheduler write-progress timeout and functional descriptor prefetch. |
| 0.94 | 2026-07-07 | seang | Documented the kick-burst fast-path interface (top-level `i_kick_burst_mask` / `i_kick_burst_addr` ports) that starts any subset of channels on a single clock cycle, bypassing the serial APB `CHn_CTRL` kick — added the interface signal table + semantics to `ch04_interfaces/02_apb4_slave.md`. Reference integration is the NexysA7 char harness (`CH_KICK_ADDR` shadow registers + `KICK_GO` bitmask CSR). |
| 0.95 | 2026-07-09 | seang | Documented read-ahead descriptor prefetch: the scheduler read side advances to the next chained legacy descriptor while the write side drains the current one, eliminating the per-descriptor boundary bubble (cross-descriptor streaming). Added a section to `ch05_performance/01_throughput.md` with on-silicon A/B (Nexys A7, single bitstream: 95.3% datapath util prefetch-on vs 76.1% off at 64-beat descriptors; row-major EXT 99.7% util bubble-free; transpose single-beat latency-bound). Runtime `SCHED_CONFIG.RD_PREFETCH_EN`, default on. |

: Document Revision History

---

**Last Updated:** 2026-07-02
