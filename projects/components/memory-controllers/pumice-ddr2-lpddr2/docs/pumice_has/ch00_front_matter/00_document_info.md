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

## DDR2 / LPDDR2 Family Controller Hardware Architecture Specification

**Document Number:** DDR2-LPDDR2-HAS-001
**Version:** 0.4
**Status:** Draft - reconciled with rearchitected RTL
**Classification:** Open Source - Apache 2.0 License

---

## Document Purpose

This Hardware Architecture Specification (HAS) provides a high-level architectural overview of the DDR2 / LPDDR2 unified memory controller family. It describes the system-level design, external interfaces, characterization parameters, and integration requirements without detailing internal implementation specifics.

**Target Audience:**

- System architects evaluating the controller for SoC integration
- Hardware engineers planning RTL implementation
- Verification engineers planning system-level testing
- Software engineers developing low-level memory configuration

**Companion Documents:**

- DDR2/LPDDR2 Family Controller Pre-Architecture Spec (`../pre-aspec.md`) — bullet-form architecture rationale
- DDR2/LPDDR2 Paging and Refresh Notes (`../paging-refresh-notes.md`) — research-derived parameter sources

---

## Revision History

| Version | Date       | Author       | Notes                                                            |
|---------|------------|--------------|------------------------------------------------------------------|
| 0.1     | 2026-06-13 | RTL Design Sherpa | First sketch — module decomposition                         |
| 0.2     | 2026-06-14 | RTL Design Sherpa | Top-level interface port list (§2.4), FUB SWAG (§2.5), family-wide config-bit registry (§5.4), multi-rank support across §2 / §3.3 / §3.4 / §3.6 / §5.2 / §6.3 |
| 0.3     | 2026-07-07 | RTL Design Sherpa | Narrow-device (x16) support: distinguish DRAM beat vs physical device word (`DRAM_DEVICE_WIDTH`); device-word column granularity + burst-length scaling; `DFI_PHASE` (rd/wr phase) CSR. Fixes on-silicon DDR2 read failure (Nexys A7 x16 bring-up). |
| 0.4     | 2026-07-12 | RTL Design Sherpa | Full reconciliation with the rearchitected RTL: three-layer core (`pumice_axi4_ifc` / `pumice_mem_cmd_scheduler` / `pumice_dfi_layer`); FSM-free `bank_timer`; de-FSM'd CAMs; single `ADDR_MAP.bank_lsb` address knob (scheme selector retired); fully-functional LPDDR2 (bit-exact JESD209-2F CA + JEDEC MR init); host-width `pumice_top_geared` gearing; block/hierarchy diagrams regenerated. |

---

## Scope of This Document

This HAS describes a single parameterized memory controller covering DDR2 and LPDDR2. It defines:

- External interfaces (AXI4 slave, DFI v2.1 master, APB CSR slave)
- Module-level decomposition and behavioral specification
- Build-time and run-time configuration parameters
- Initialization, power-state, and refresh policies
- Verification strategy and characterization plan

It does not define:

- Bit-level pin assignments (the SystemVerilog port list in `regs/pumice_ctrl_ports.svh` is the canonical wire-level source)
- Detailed timing diagrams (deferred to v0.3)
- Verilog package skeletons or RTL stubs
- Floorplan or layout guidance

---

## Out of Scope

The following features are explicitly out of scope for this version of the controller and will be addressed in higher-generation family controllers or future revisions:

- Inline ECC
- DFI training, frequency-change, and low-power sub-interfaces
- AXI exclusive access semantics
- Bank groups (not present in DDR2 / LPDDR2)
- Command/Address parity, CRC, Data Bus Inversion (not present in DDR2 / LPDDR2)
