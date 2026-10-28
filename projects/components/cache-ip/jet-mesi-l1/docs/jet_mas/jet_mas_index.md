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

# jet MAS Index

**Version:** 0.1
**Date:** 2026-10-28
**Purpose:** Micro-architecture specification for the jet lockup-free MESI
snoopy L1 cache
**Scope:** Cycle-level behavior, per-module micro-architecture, and signal
contracts for `jet_top` (pair-rig top) and `jet_ace_top` (onyx-rig top).
The shared arrays, replacement engine, fill/drain engines, and snoop
responder come unchanged from `cache-ip/common-ip/` (the `l1_*` FUBs amber
landed); jet owns `jet_control`, `jet_mshr`, `jet_wb_buffer`, `jet_rsp_seq`,
`jet_ace_issue`, and the two tops. The binding architecture lives in the
[jet HAS](../jet_has/jet_has_index.md); the J1–J7 rulings are recorded in
the [jet PRD](../../PRD.md).

**Status warning:** no jet RTL exists at 0.1 — every chapter is a contract
for the landing implementation.

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture and What the MAS Covers](ch01_overview/01_architecture.md)
- [Top-Level Port List](ch01_overview/02_port_list.md)
- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### Chapter 2: Functional Blocks

- [jet_control: Lookup/Commit Pipeline](ch02_blocks/01_jet_control.md)
- [jet_mshr: the MAB File](ch02_blocks/02_jet_mshr.md)
- [jet_wb_buffer: Decoupled Writeback Buffer](ch02_blocks/03_jet_wb_buffer.md)
- [jet_rsp_seq: Response Sequencer](ch02_blocks/04_jet_rsp_seq.md)
- [The Snoop Path Under Concurrency](ch02_blocks/05_snoop_path.md)
- [Fill and Drain Engines](ch02_blocks/06_fill_drain.md)
- [CPU Front End and l1_monlite](ch02_blocks/07_frontend_monlite.md)

### Chapter 3: Interfaces

- [CPU GAXI Request/Response Timing](ch03_interfaces/01_cpu_gaxi.md)
- [Fabric AXI4 Master Timing](ch03_interfaces/02_fabric_axi4.md)
- [Fabric ACE Master Timing](ch03_interfaces/03_fabric_ace.md)
- [Snoop AC/CD/CR Timing and Ordering](ch03_interfaces/04_snoop_accdcr.md)
- [MonBus Event Emission Points](ch03_interfaces/05_monbus_timing.md)

### Chapter 4: MonBus Observation Map

- [Event Encodings and Emission Points](ch04_monbus_observation/01_event_map.md)
- [Drop-and-Count Behavior and monbus_tally_axil](ch04_monbus_observation/02_tally_integration.md)

### Chapter 5: Verification

- [Formal Targets (Liveness and Safety)](ch05_verification/01_formal_targets.md)
- [DV Plan: the Ladder and the Scoreboard](ch05_verification/02_dv_plan.md)
- [gem5 FSM Cross-Check](ch05_verification/03_gem5_crosscheck.md)

### Chapter 6: Configuration

- [Elaboration Configurations](ch06_configuration/01_elaboration_configs.md)
- [DV Matrix Dimensions](ch06_configuration/02_dv_matrix.md)

## Quick Reference

### Shared blocks (from `cache-ip/common-ip`, unchanged)

| Module | Role in jet |
|--------|-------------|
| `l1_tag_array` / `l1_data_array` | dual-port tag+state / data store; port A CPU/fill, port B snoop |
| `l1_repl` | victim way selection (LRU / tree-PLRU / FIFO / RANDOM) |
| `l1_fill` | line-fill AXI4 read sequencing (single ID) |
| `l1_drain` | write-back AXI4 write sequencing |
| `l1_snoop_resp` | ACE-shaped snoop adapter (AC/CR/CD) |
| `l1_cpu_frontend` | GAXI slave request/response latch |
| `l1_monlite` | drop-and-count MonBus observer (extended for J7 classes) |
| `l1_pkg` | geometry, MESI encodings, snoop types |

### jet blocks (new)

| Module | Role |
|--------|------|
| `jet_control` | lookup/commit pipeline: classify, allocate, merge, commit, release |
| `jet_mshr` | MAB file: full-assoc CAM of outstanding misses, `MSHR_COUNT` 2–16 (default 8) |
| `jet_wb_buffer` | decoupled writeback buffer, `VICTIM_DEPTH` 1–4 (default 2) |
| `jet_rsp_seq` | issue-order response release (J4) |
| `jet_ace_issue` | cache events → ACE coherent transactions (jet_ace_top) |
| `jet_top` / `jet_ace_top` | the two rig tops |

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| jet PRD | [../../PRD.md](../../PRD.md) | **binding requirements** — J1–J7 and success criteria |
| jet HAS | [../jet_has/jet_has_index.md](../jet_has/jet_has_index.md) | architecture specification this MAS implements |
| jet design spec | [../../../../../../docs/superpowers/specs/2026-10-28-jet-mshr-design.md](../../../../../../docs/superpowers/specs/2026-10-28-jet-mshr-design.md) | the approved design narrative |
| amber MAS | [../../../amber-mesi-l1/docs/amber_mas/amber_mas_index.md](../../../amber-mesi-l1/docs/amber_mas/amber_mas_index.md) | sibling blueprint, landed-RTL reference |
| onyx PRD | [../../../onyx-ace-ccu/PRD.md](../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the snoop port |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| gem5 Ruby protocols | [../../../References/gem5-ruby-protocols/README.md](../../../References/gem5-ruby-protocols/README.md) | golden-protocol source for the oracle |
| Chinnakonda | local Calibre conversion (`/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/`) | micro-architecture playbook this design follows (§9.8, §10.6–10.12, §8) |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

**Last Updated:** 2026-10-28
**Maintained By:** jet architecture
