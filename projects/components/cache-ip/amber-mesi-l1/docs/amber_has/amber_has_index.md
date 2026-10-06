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

# amber — Blocking MESI Snoopy L1 Cache — Hardware Architecture Specification

**Version:** 1.0
**Date:** 2026-10-06
**Status:** full HAS ratifies the Pre-HAS sketch; PRD decisions D1, D2, D4, D5, D6, D7, D8, D9, D10 are DECIDED. D3 (memory-side shape) and D11 (array construction) remain OPEN and are recorded honestly in the chapters they shape.

**Scope:** The architecture of `amber` (pair-rig top) and `amber_ace` (onyx-rig top) from the CPU GAXI slave through the shared cache core to the fabric masters and ACE snoop responder. The [MAS](../amber_mas/amber_mas_index.md) closes the micro-architecture decisions this book defers.

**How this book relates to its sources.** The [amber PRD](../../PRD.md) is the binding requirements document. This HAS carries the Pre-HAS feature sketches (F1–F18) forward, drops their "PROPOSED" hedging where the PRD has decided, and fixes the module set and interfaces as architecture. Where D3 and D11 are still open, the chapters state the current direction and the consequences; nothing is disguised as decided. The [GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) reset-macro, array-syntax, no-bespoke-SRAM, and filelist rules apply throughout.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose.md)
- [Document Conventions](ch01_introduction/02_conventions.md)
- [Definitions and Acronyms](ch01_introduction/03_definitions.md)

### Chapter 2: System Overview

- [Use Cases](ch02_overview/01_use_cases.md)
- [Key Features](ch02_overview/02_key_features.md)
- [System Context](ch02_overview/03_system_context.md)
- [Block Diagram](ch02_overview/04_block_diagram.md)

### Chapter 3: Architecture

- [Top Structure and the Two Rigs](ch03_architecture/01_top_structure.md)
- [Data Flow: Hits, Misses, Fills, and Drains](ch03_architecture/02_data_flow.md)
- [Control FSM: Blocking Pipeline and Pending-Fill Bypass](ch03_architecture/03_control_fsm.md)
- [Coherence FSM and the Snoop Responder](ch03_architecture/04_coherence_fsm.md)
- [Arbitration and the Victim Bypass](ch03_architecture/05_arbitration_bypass.md)

### Chapter 4: Interfaces

- [CPU-Side GAXI Slave](ch04_interfaces/01_cpu_gaxi.md)
- [Fabric-Side AXI4 Masters](ch04_interfaces/02_fabric_axi4.md)
- [Fabric-Side ACE Masters and Coherent Issue](ch04_interfaces/03_fabric_ace.md)
- [Snoop Port: AC/CD/CR Adapter](ch04_interfaces/04_snoop_accdcr.md)
- [Observation: MonBus through amber_monlite](ch04_interfaces/05_observation_monbus.md)

### Chapter 5: Parameters

- [amber_pkg and Build-Time Geometry](ch05_parameters/01_parameters.md)

### Chapter 6: Integration

- [Clocking and Reset](ch06_integration/01_clocking_reset.md)
- [Verification Strategy](ch06_integration/02_verification.md)
- [Characterization](ch06_integration/03_characterization.md)
- [Future Hooks](ch06_integration/04_future_hooks.md)

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| 2.1 | `assets/mermaid/01_block_diagram.mmd` | amber shared core, the two rig tops, and the peer/onyx snoop boundary |
| 3.1 | `assets/mermaid/02_miss_flow.mmd` | miss-to-fill-to-replay data flow, with victim drain |
| 3.2 | `assets/mermaid/03_snoop_flow.mmd` | probe path through tag port B and the pending-fill bypass |

: Table 0.0: Figures and their sources

---

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| amber PRD | [../../PRD.md](../../PRD.md) | **binding requirements** — all D-rows and success criteria originate here |
| amber Pre-HAS | [./amber_prehas.md](./amber_prehas.md) | architecture sketch; this HAS supersedes and ratifies it |
| amber MAS | [../amber_mas/amber_mas_index.md](../amber_mas/amber_mas_index.md) | micro-architecture and pre-RTL signal-contract / kmap workbook |
| jet PRD | [../../../jet-mesi-l1/PRD.md](../../../jet-mesi-l1/PRD.md) | lockup-free follow-on; amber must not silently pre-decide jet's J-rows |
| onyx PRD | [../../../onyx-ace-ccu/PRD.md](../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the ACE-shaped snoop port; onyx D2 defines the coherent-transaction subset |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| gem5 Ruby protocols | [../../../References/gem5-ruby-protocols/README.md](../../../References/gem5-ruby-protocols/README.md) | golden-protocol source for the Python reference model and FSM oracles |
| cache simulator | [../../../../../../bin/apps/cache_sim/README.md](../../../../../../bin/apps/cache_sim/README.md) | golden parity model for LRU/FIFO/RANDOM |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

: Table 0.1: Related documentation

---

**Last Updated:** 2026-10-06
**Maintained By:** amber architecture
