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

# onyx — Snoop-Based ACE Coherency Unit — Hardware Architecture Specification

**Version:** 0.3
**Date:** 2026-11-21
**Status:** 0.3: the D rows decided (PRD v0.7, 2026-11-20) and the RTL built -- `onyx_ccu`, jet-prime's pair fabric generalized to N ports, verified on jet-prime's pair-rig grid, argued formally at two ports and measured on the Genesys2 reference rig (onyx TASK-001, 2026-11-21). Open: the ACE-Lite IO port (D1), the MonBus taps (D9), the N rows other than N1.

**Scope:** The architecture of `onyx` as the snoop-based ACE coherency manager for the `cache-ip/` family. This book records the port contracts that are decided (D7), the design-invariant landscape proposed by the PRD, and the open decisions that must close before the manager architecture can be fixed. It does not invent answers for the open rows.

**How this book relates to its sources.** The [onyx PRD](../../PRD.md) is the binding requirements document. The [AMBA ACE Interface Definition](../../../References/AMBA_ACE_Interface_Definition.md) is the normative in-repo contract for the ACE-shaped ports. The [cache-ip README](../../../README.md) gives the family context. Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, supplies the background and candidate invariants cited in the chapters that use it. The [GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) reset-macro, array-syntax, no-bespoke-SRAM, and filelist rules apply throughout.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose](ch01_introduction/01_purpose.md)
- [Scope and Non-Goals](ch01_introduction/02_scope.md)

### Chapter 2: System Overview

- [Use Cases](ch02_overview/01_use_cases.md)
- [Key Features](ch02_overview/02_key_features.md)
- [System Context](ch02_overview/03_system_context.md)
- [Block Diagram](ch02_overview/04_block_diagram.md)

### Chapter 3: Architecture

- [Manager Pipeline](ch03_architecture/01_manager_pipeline.md)
- [Coherence Decision Layer](ch03_architecture/02_coherence_decision_layer.md)
- [Serializer and Point of Serialization](ch03_architecture/03_serializer_pos.md)
- [Snoop Fanout and Response Gather](ch03_architecture/04_fanout_gather.md)

### Chapter 4: Interfaces

- [Cache-Side ACE Ports](ch04_interfaces/01_cache_side_ace.md)
- [Memory-Side AXI4 Master](ch04_interfaces/02_memory_side_axi4.md)
- [Snoop Fanout Port](ch04_interfaces/03_snoop_fanout.md)
- [Observation: MonBus](ch04_interfaces/04_observation_monbus.md) — D9 decided; the taps are a later TASK-001 step

### Chapter 5: Parameters

- [Build-Time Geometry](ch05_parameters/01_parameters.md)

### Chapter 6: Integration

- [Verification Strategy](ch06_integration/01_verification.md)
- [Characterization](ch06_integration/02_characterization.md)
- [Future Hooks](ch06_integration/03_future_hooks.md)

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| 2.1 | `assets/graphviz/01_block_diagram.dot` | the manager shape as planned before the D rows closed; the blocks are the built ones ([Chapter 2.4](ch02_overview/04_block_diagram.md)), a redraw from the RTL is pending |

: Table 0.0: Figures and their sources

---

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| onyx PRD | [../../PRD.md](../../PRD.md) | **binding requirements** — all D/N rows and success criteria originate here |
| cache-ip README | [../../../README.md](../../../README.md) | family context: amber, jet, onyx, and the ACE-shaped interface decision |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H; the normative reference for the ACE-shaped ports |
| amber HAS | [../../../amber-mesi-l1/docs/amber_has/amber_has_index.md](../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) | the cache that onyx manages; D7 decided the onyx↔amber adapter boundary together with amber D4 |
| jet HAS | [../../../jet-mesi-l1/docs/jet_has/jet_has_index.md](../../../jet-mesi-l1/docs/jet_has/jet_has_index.md) | lockup-free cache; the same onyx interface and D2 subset will apply |
| amber PRD | [../../../amber-mesi-l1/PRD.md](../../../amber-mesi-l1/PRD.md) | amber D10 is onyx's first consumer (the pair rig grown by one block) |
| jet PRD | [../../../jet-mesi-l1/PRD.md](../../../jet-mesi-l1/PRD.md) | future onyx-rig consumer; onyx must not pre-decide jet's open J-rows |
| culsans | `pulp-platform/culsans` — `rtl/src/ace_ccu_top.sv` | worked example of a snoop-based ACE CCU; not a dependency |
| gem5 Ruby protocols | [../../../References/gem5-ruby-protocols/README.md](../../../References/gem5-ruby-protocols/README.md) | executable transient-state tables; source for the Python golden model |
| cache simulator | [../../../../../../vault/handbook/tools/apps/cache-sim.md](../../../../../../vault/handbook/tools/apps/cache-sim.md) | golden parity model for hit-rate cross-checks |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* | local Calibre conversion, outside the repo: `/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/index.md` | background and candidate invariants; sections cited in the chapters that use them |

: Table 0.1: Related documentation

---

**Last Updated:** 2026-10-11
**Maintained By:** onyx architecture
