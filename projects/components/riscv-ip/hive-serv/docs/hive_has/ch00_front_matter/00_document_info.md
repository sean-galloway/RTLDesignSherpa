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

## HIVE Hardware Architecture Specification

**Document Number:** HIVE-HAS-001
**Version:** 0.2
**Status:** Draft (pre-RTL — specification phase)
**Classification:** Open Source - MIT License

---

## Document Purpose

This Hardware Architecture Specification (HAS) defines the external, system-level
architecture of the HIVE subsystem (Hierarchical Intelligent Vector Environment):
what it is, what it controls, how it connects to the host, the RAPIDS DMA engine,
and the Delta Network, how packets and registers are encoded at its boundaries,
and how it is integrated into a larger system. It is written for consumers of the
subsystem — integrators, firmware engineers, and verification engineers — and is
deliberately interface-first: ports, packet formats, encodings, and protocols,
with rationale where boundary behavior is a design decision rather than an
obvious default.

This document does not describe the internal microarchitecture. Block internals,
cycle-level behavior, clock/reset implementation detail, and the verification
hook plan live in the companion Micro-Architecture Specification (MAS).

**Target Audience:**
- System architects evaluating HIVE for integration alongside RAPIDS and Delta
- Hardware engineers wiring HIVE into a system top level
- Firmware engineers writing HIVE-C control software or SERV monitor firmware
- Verification engineers planning subsystem-level and system-level test coverage

**Companion Documents:**
- HIVE Micro-Architecture Specification (MAS) - internal block-level implementation intent
- HIVE PRD (`PRD.md`) - product requirements, use cases, and roadmap
- RAPIDS Beats HAS/MAS - the DMA engine HIVE-C controls
- Delta HAS/MAS - the network HIVE-C and the SERV monitors inject packets into

---

## References

| ID | Document | Description |
|----|----------|-------------|
| [REF-1] | HIVE MAS v0.2 (`docs/hive_mas/`) | Micro-Architecture Specification (companion) |
| [REF-2] | HIVE PRD (`PRD.md`) | Product requirements and use cases |
| [REF-3] | RAPIDS Beats HAS (`../../../../../dma-ip/rapids/docs/rapids_beats_has/rapids_beats_has_index.md`) | RAPIDS DMA engine; CDA consumer |
| [REF-4] | Delta HAS (`../../../../../fabric-gen-ip/delta/docs/delta_has/delta_has_index.md`) | 4×4 mesh NoC; packet routing fabric |
| [REF-5] | AXI4-Stream Protocol Specification, ARM IHI 0051A | AXIS signal semantics (TUSER/TID/TDEST/TLAST) |
| [REF-6] | VexRiscv (https://github.com/SpinalHDL/VexRiscv) | HIVE-C master core generator |
| [REF-7] | SERV (https://github.com/olofk/serv) | Bit-serial RV32I core used for the 16 monitors |
| [REF-8] | RISC-V Falcon Suite README (`../README.md`) | Suite ladder and hive-serv placement beside it |

: Reference Documents

---

## Terminology

| Term | Definition |
|------|------------|
| CDA | Compute Direct Access — the packet class (TUSER=2'b01) HIVE-C uses to inject RAPIDS descriptors inband |
| Context | One of 4 pre-loaded routing configurations (systolic, mesh, tree, custom) held by the Configuration Manager |
| Control Network | Dedicated low-bandwidth star network between HIVE-C and the 16 SERV monitors, separate from the Delta data path |
| HIVE-C | The HIVE master controller: one VexRiscv RV32IM core, Delta Virtual Tile 17 |
| Inband Control | Control messages carried through the data network as packets rather than over a separate memory-mapped bus |
| Monitors | The 16 SERV-based per-tile traffic monitors (not to be confused with verification monitors) |
| PKT_DATA / PKT_CONFIG / PKT_STATUS | AXIS packet classes encoded in TUSER[1:0]: 2'b00 compute data, 2'b10 configuration, 2'b11 status |
| Quiesce | The drain-and-hold protocol that empties the network before an atomic context switch |
| SERV | Small Embedded RISC-V — bit-serial RV32I core, ~125 LUTs per instance |
| Virtual Tile | A Delta Network endpoint that is not a physical compute tile: 16 = RAPIDS, 17 = HIVE-C |
| VexRiscv | SpinalHDL-generated RISC-V core family; HIVE-C uses the "Small" RV32IM configuration |

: Terminology and Definitions

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 0.1 | 2026-10-12 | seang | Initial HAS release. Migrates and supersedes the v0.3 `hive_spec/` + `hive_specification.md` drafts; resource-budget table corrected (HIVE-only vs. system subtotals disambiguated); delta references repointed to `fabric-gen-ip/delta` |
| 0.2 | 2026-10-13 | seang | Owner decisions recorded: fabric IDLE status register (PeakRDL bank) is the quiesce check; kestrel loader pattern for firmware load; descriptor mailbox parameter-controlled with dedicated register file default (custom-instruction alternative rejected) |

: Document Revision History

---

**Last Updated:** 2026-10-13
