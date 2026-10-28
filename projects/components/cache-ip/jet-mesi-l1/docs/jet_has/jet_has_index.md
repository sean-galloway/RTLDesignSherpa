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

# jet — Lockup-Free MESI Snoopy L1 Cache — Hardware Architecture Specification

**Version:** 0.3
**Date:** 2026-10-28
**Status:** 0.3: J1–J7 CLOSED (Sean, 2026-10-28). All seven decisions are recorded in the PRD and in ch03/ch05/ch06; the cycle-level architecture moves to the jet MAS.

**Scope:** The architecture of `jet` (pair-rig top) and `jet_ace` (onyx-rig top) as a lockup-free upgrade of `amber`. This book records what is inherited unchanged from amber, the research question jet exists to answer, and the decided J-rows that shape the MSHR delta.

**How this book relates to its sources.** The [jet PRD](../../PRD.md) is the binding requirements document. The [amber HAS](../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) is the inherited architecture: amber's core, interfaces, parameters, and integration rules apply unless a J-row explicitly overrides them. The J-rows are jet's deltas; this 0.3 HAS records their rulings and what each drives. The [GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) reset-macro, array-syntax, no-bespoke-SRAM, and filelist rules apply throughout.

---

## Document Organization

**Note:** All chapters linked below for automated document generation. Stub chapters are marked with the J-row that unblocks them.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose.md)

### Chapter 2: System Overview

- [Use Cases](ch02_overview/01_use_cases.md)
- [Key Features](ch02_overview/02_key_features.md)
- [System Context](ch02_overview/03_system_context.md)
- [Block Diagram](ch02_overview/04_block_diagram.md)

### Chapter 3: Architecture

- [MSHR Organization](ch03_architecture/01_mshr_organization.md) — J1 decided 2026-10-28
- [Snoop During Miss](ch03_architecture/02_snoop_during_miss.md) — J4/J5 decided 2026-10-28
- [Hit-Under-Miss and Miss Merging](ch03_architecture/03_hit_under_miss_and_merge.md) — J2/J3 decided 2026-10-28

### Chapter 4: Interfaces

- [Inherited amber Contracts](ch04_interfaces/01_inherited_amber_contracts.md)
- [Observation: MonBus and the J7 Measurement Classes](ch04_interfaces/02_observation_monbus.md)

### Chapter 5: Parameters

- [jet_pkg and Build-Time Geometry](ch05_parameters/01_parameters.md) — J1/J5 decided 2026-10-28

### Chapter 6: Integration

- [Clocking and Reset](ch06_integration/01_clocking_reset.md)
- [Verification Strategy](ch06_integration/02_verification.md) — J5/J6 decided 2026-10-28
- [Characterization](ch06_integration/03_characterization.md) — J7 decided 2026-10-28
- [Future Hooks](ch06_integration/04_future_hooks.md)

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| 2.1 | `assets/graphviz/01_block_diagram.dot` | the planned whole unit, drawn from the prose in [Chapter 2.4](ch02_overview/04_block_diagram.md); J1/J5 are decided, so the module set is fixed — the diagram gets its real MSHR/writeback-buffer depths when the MAS lands |

: Table 0.0: Figures and their sources

---

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| jet PRD | [jet PRD](../../PRD.md) | **binding requirements** — all J-rows and success criteria originate here |
| amber HAS | [amber HAS](../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) | inherited architecture, interfaces, parameters, and integration rules |
| onyx PRD | [onyx PRD](../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the ACE-shaped snoop port; onyx D2 defines the coherent-transaction subset |
| AMBA ACE Interface Definition | [AMBA ACE Interface Definition](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| cache simulator | [cache simulator](../../../../../../bin/apps/cache_sim/README.md) | golden parity model; jet extends it to predict concurrency numbers |
| Global Requirements | [Global Requirements](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* | local Calibre conversion, outside the repo: `/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/index.md` | background for open decisions: §7.8 (file 7.7) forward-progress guarantees, §8.2 deadlocks, §8.3 starvation, §10.8 (file 10.6) snoop snarfing, §10.10 (file 10.8) outstanding sizing, §13.4 (file 13.3) prefetch training |

: Table 0.1: Related documentation

---

**Last Updated:** 2026-10-28
**Maintained By:** jet architecture
