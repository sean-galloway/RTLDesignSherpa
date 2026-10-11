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

**Version:** 0.1
**Date:** 2026-10-11
**Status:** 0.1 skeleton: purpose, context, and the decision landscape are real content; chapters shaped by the open J-rows (J1–J7) are explicit stubs that say so and point at the open rows.

**Scope:** The architecture of `jet` (pair-rig top) and `jet_ace` (onyx-rig top) as a lockup-free upgrade of `amber`. This book records what is inherited unchanged from amber, the research question jet exists to answer, and the open decisions that must close before the architecture can be fixed. It does not invent answers for J1–J7.

**How this book relates to its sources.** The [jet PRD](../../PRD.md) is the binding requirements document. The [amber HAS](../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) is the inherited architecture: amber's core, interfaces, parameters, and integration rules apply unless a J-row explicitly overrides them. The open J-rows are jet's deltas; this 0.1 HAS records their decision landscape, not their answers. The [GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) reset-macro, array-syntax, no-bespoke-SRAM, and filelist rules apply throughout.

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

- [MSHR Organization](ch03_architecture/01_mshr_organization.md) — stub, blocked on J1
- [Snoop During Miss](ch03_architecture/02_snoop_during_miss.md) — stub, blocked on J4/J5
- [Hit-Under-Miss and Miss Merging](ch03_architecture/03_hit_under_miss_and_merge.md) — stub, blocked on J2/J3

### Chapter 4: Interfaces

- [Inherited amber Contracts](ch04_interfaces/01_inherited_amber_contracts.md)
- [Observation: MonBus and the J7 Measurement Classes](ch04_interfaces/02_observation_monbus.md)

### Chapter 5: Parameters

- [jet_pkg and Build-Time Geometry](ch05_parameters/01_parameters.md) — stub, blocked on J1/J5

### Chapter 6: Integration

- [Clocking and Reset](ch06_integration/01_clocking_reset.md)
- [Verification Strategy](ch06_integration/02_verification.md) — stub, blocked on J5/J6
- [Characterization](ch06_integration/03_characterization.md) — stub, blocked on J7
- [Future Hooks](ch06_integration/04_future_hooks.md)

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| *none* | — | Figures are empty at 0.1; the block diagram is described in prose in [Chapter 2.4](ch02_overview/04_block_diagram.md) and will be drawn after J1/J5 close. |

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
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* | [Chinnakonda, *Designing a Multiprocessor Cache Subsystem*](../../../../../../../calibre/books/designing-a-multiprocessor-cache-subsystem/index.md) | background for open decisions: §7.8 (file 7.7) forward-progress guarantees, §8.2 deadlocks, §8.3 starvation, §10.8 (file 10.6) snoop snarfing, §10.10 (file 10.8) outstanding sizing, §13.4 (file 13.3) prefetch training |

: Table 0.1: Related documentation

---

**Last Updated:** 2026-10-11
**Maintained By:** jet architecture
