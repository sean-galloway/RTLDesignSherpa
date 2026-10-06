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

# amber MAS Index

**Version:** 1.0
**Date:** 2026-10-06
**Purpose:** Micro-architecture specification for the amber blocking MESI snoopy L1 cache

**Scope:** Cycle-level behavior, per-module micro-architecture, and the pre-RTL signal-contract / kmap workbook for `amber` (pair-rig top) and `amber_ace` (onyx-rig top). The binding architecture lives in the [amber HAS](../amber_has/amber_has_index.md); this book closes the implementation decisions the HAS deferred.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture and What the MAS Covers](ch01_overview/01_architecture.md)
- [Top-Level Port List](ch01_overview/02_port_list.md)
- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### Chapter 2: Functional Blocks

- [amber_control: Blocking Pipeline FSM](ch02_blocks/01_amber_control.md)
- [Pending-Fill Bypass Register](ch02_blocks/02_pending_fill_bypass.md)
- [amber_tag_array and amber_data_array](ch02_blocks/03_tag_data_arrays.md)
- [amber_repl: Replacement Policy Engine](ch02_blocks/04_amber_repl.md)
- [amber_victim: Depth-1 Victim Buffer](ch02_blocks/05_amber_victim.md)
- [amber_fill and amber_drain](ch02_blocks/06_fill_drain.md)
- [amber_snoop_resp: Snoop Responder Adapter](ch02_blocks/07_amber_snoop_resp.md)
- [amber_ace_issue: Coherent Transaction Mapping](ch02_blocks/08_amber_ace_issue.md)
- [amber_cpu_frontend and amber_monlite](ch02_blocks/09_frontend_monlite.md)

### Chapter 3: Interfaces

- [CPU GAXI Request/Response Timing](ch03_interfaces/01_cpu_gaxi.md)
- [Fabric AXI4 Master Timing](ch03_interfaces/02_fabric_axi4.md)
- [Fabric ACE Master Timing](ch03_interfaces/03_fabric_ace.md)
- [Snoop AC/CD/CR Timing and Ordering](ch03_interfaces/04_snoop_accdcr.md)
- [MonBus Event Emission Points](ch03_interfaces/05_monbus_timing.md)

### Chapter 4: MonBus Observation Map

- [Event Encodings and Emission Points](ch04_monbus_observation/01_event_map.md)
- [Drop-and-Count Behavior and monbus_tally_axil](ch04_monbus_observation/02_tally_integration.md)

### Chapter 5: Verification Bring-Up

- [What the K-maps Prove](ch05_verification/01_kmap_verdicts.md)
- [RTL Landing Diff Procedure](ch05_verification/02_rtl_diff.md)
- [gem5 FSM Cross-Check](ch05_verification/03_gem5_crosscheck.md)

### Chapter 6: Configuration

- [Elaboration Configurations](ch06_configuration/01_elaboration_configs.md)
- [DV Matrix Dimensions](ch06_configuration/02_dv_matrix.md)

---

## Quick Reference

### Core Blocks

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| `amber_control` | `rtl/fub/amber_control.sv` | Blocking pipeline FSM, state encoding, miss/replay sequencing | Pre-RTL contract |
| `amber_tag_array` | `rtl/fub/amber_tag_array.sv` | Dual-port `sdpram_core` tag + MESI state store | Pre-RTL contract |
| `amber_data_array` | `rtl/fub/amber_data_array.sv` | Dual-port `sdpram_core` data store | Pre-RTL contract |
| `amber_repl` | `rtl/fub/amber_repl.sv` | LRU / tree-PLRU / FIFO / RANDOM replacement | Pre-RTL contract |
| `amber_victim` | `rtl/fub/amber_victim.sv` | Depth-1 dirty victim buffer | Pre-RTL contract |
| `amber_fill` | `rtl/fub/amber_fill.sv` | Line-fill read master interface | Pre-RTL contract |
| `amber_drain` | `rtl/fub/amber_drain.sv` | Dirty victim write-back interface | Pre-RTL contract |
| `amber_snoop_resp` | `rtl/fub/amber_snoop_resp.sv` | ACE snoop adapter, CR/CD ordering | Pre-RTL contract |
| `amber_ace_issue` | `rtl/fub/amber_ace_issue.sv` | Cache events → ACE transactions | Pre-RTL contract |
| `amber_cpu_frontend` | `rtl/fub/amber_cpu_frontend.sv` | GAXI slave request/response latch | Pre-RTL contract |
| `amber_monlite` | `rtl/fub/amber_monlite.sv` | Drop-and-count MonBus observer | Pre-RTL contract |

### Top Modules

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| `amber` | `rtl/top/amber.sv` | Pair-rig top, AXI4 memory + ACE snoop | Pre-RTL contract |
| `amber_ace` | `rtl/top/amber_ace.sv` | Onyx-rig top, full ACE coherent issue | Pre-RTL contract |
| `amber_core` | `rtl/macro/amber_core.sv` | Shared core (both rigs) | Pre-RTL contract |

---

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| amber PRD | [../../PRD.md](../../PRD.md) | **binding requirements** — all D-rows and success criteria originate here |
| amber HAS | [../amber_has/amber_has_index.md](../amber_has/amber_has_index.md) | architecture specification this MAS implements |
| amber Pre-HAS | [../amber_has/amber_prehas.md](../amber_has/amber_prehas.md) | original feature sketches |
| K-map / signal-contract workbook | [../gen_amber_contracts_kmaps.py](../gen_amber_contracts_kmaps.py) | pre-RTL combinational-contract sheets and kmaps |
| jet PRD | [../../../jet-mesi-l1/PRD.md](../../../jet-mesi-l1/PRD.md) | lockup-free follow-on; amber must not pre-decide jet's J-rows |
| onyx PRD | [../../../onyx-ace-ccu/PRD.md](../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the ACE-shaped snoop port; onyx D2 defines the coherent-transaction subset |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| gem5 Ruby protocols | [../../../References/gem5-ruby-protocols/README.md](../../../References/gem5-ruby-protocols/README.md) | golden-protocol source for the Python reference model and FSM oracles |
| cache simulator | [../../../../../../bin/apps/cache_sim/README.md](../../../../../../bin/apps/cache_sim/README.md) | golden parity model for LRU/FIFO/RANDOM |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

---

**Last Updated:** 2026-10-06
**Maintained By:** amber architecture
