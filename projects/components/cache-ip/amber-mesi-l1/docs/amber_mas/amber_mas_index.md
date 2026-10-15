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

**Version:** 0.7
**Date:** 2026-10-15
**Purpose:** Micro-architecture specification for the amber blocking MESI snoopy L1 cache

**Scope:** Cycle-level behavior, per-module micro-architecture, and the signal-contract / kmap workbook for `amber_top` (pair-rig top) and `amber_ace_top` (onyx-rig top). The shared cache core is `l1_core` and its `l1_*` FUBs in `cache-ip/common-ip/`; amber owns the two tops, `amber_ace_issue`, and the pair-rig fabric. The binding architecture lives in the [amber HAS](../amber_has/amber_has_index.md); this book closes the implementation decisions the HAS deferred.

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

- [l1_control: Blocking Pipeline FSM](ch02_blocks/01_l1_control.md)
- [Pending-Fill Bypass Register (l1_pending_fill_bypass)](ch02_blocks/02_pending_fill_bypass.md)
- [l1_tag_array and l1_data_array](ch02_blocks/03_tag_data_arrays.md)
- [l1_repl: Replacement Policy Engine](ch02_blocks/04_l1_repl.md)
- [l1_victim: Depth-1 Victim Buffer](ch02_blocks/05_l1_victim.md)
- [l1_fill and l1_drain](ch02_blocks/06_fill_drain.md)
- [l1_snoop_resp: Snoop Responder Adapter](ch02_blocks/07_l1_snoop_resp.md)
- [amber_ace_issue: Coherent Transaction Mapping](ch02_blocks/08_amber_ace_issue.md)
- [l1_cpu_frontend and l1_monlite](ch02_blocks/09_frontend_monlite.md)

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

### Core Blocks (shared L1 core, `cache-ip/common-ip`)

| Module | File | Purpose |
|--------|------|---------|
| `l1_control` | `cache-ip/common-ip/rtl/fub/l1_control.sv` | Blocking pipeline FSM, state encoding, miss/replay sequencing |
| `l1_pending_fill_bypass` | `cache-ip/common-ip/rtl/fub/l1_pending_fill_bypass.sv` | Pending-fill bypass register (leaf of `l1_control`) |
| `l1_victim` | `cache-ip/common-ip/rtl/fub/l1_victim.sv` | Depth-1 dirty victim buffer (leaf of `l1_control`) |
| `l1_tag_array` | `cache-ip/common-ip/rtl/fub/l1_tag_array.sv` | Dual-port `sdpram_core` tag + MESI state store |
| `l1_data_array` | `cache-ip/common-ip/rtl/fub/l1_data_array.sv` | Dual-port `sdpram_core` data store |
| `l1_repl` | `cache-ip/common-ip/rtl/fub/l1_repl.sv` | LRU / tree-PLRU / FIFO / RANDOM replacement |
| `l1_fill` | `cache-ip/common-ip/rtl/fub/l1_fill.sv` | Line-fill read master interface |
| `l1_drain` | `cache-ip/common-ip/rtl/fub/l1_drain.sv` | Dirty victim write-back interface |
| `l1_snoop_resp` | `cache-ip/common-ip/rtl/fub/l1_snoop_resp.sv` | ACE snoop adapter, CR/CD ordering |
| `l1_snoop_kmap` | `cache-ip/common-ip/rtl/fub/l1_snoop_kmap.sv` | Snoop-response decision logic as a standalone K-map-checked block (unit-tested; not instantiated by `l1_core`) |
| `l1_cpu_frontend` | `cache-ip/common-ip/rtl/fub/l1_cpu_frontend.sv` | GAXI slave request/response latch |
| `l1_monlite` | `cache-ip/common-ip/rtl/fub/l1_monlite.sv` | Drop-and-count MonBus observer |
| `l1_pkg` | `cache-ip/common-ip/rtl/includes/l1_pkg.sv` | Geometry defaults, MESI encodings, snoop types |

### amber Blocks and Top Modules

| Module | File | Purpose |
|--------|------|---------|
| `l1_core` | `cache-ip/common-ip/rtl/top/l1_core.sv` | Shared core (both rigs): structural integration of the `l1_*` FUBs |
| `amber_top` | `amber-mesi-l1/rtl/top/amber_top.sv` | Pair-rig top: `l1_core` + `axi4_master_rd/wr_monlite` + `monbus_arbiter` |
| `amber_ace_top` | `amber-mesi-l1/rtl/top/amber_ace_top.sv` | Onyx-rig top: `l1_core` + `amber_ace_issue` + `axi4ace_master_rd/wr_monlite` + `monbus_arbiter` |
| `amber_ace_issue` | `amber-mesi-l1/rtl/fub/amber_ace_issue.sv` | Cache events → ACE coherent transactions |
| `amber_pair_fabric` | `amber-mesi-l1/rtl/top/amber_pair_fabric.sv` | Minimal two-master snoopy manager for the pair rig (DV) |

The RTL for every block above exists; the per-block chapters in Chapter 2 were written as the contracts it was built against, and the K-map verdict procedure in Chapter 5 compares the two.

---

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| amber PRD | [../../PRD.md](../../PRD.md) | **binding requirements** — all D-rows and success criteria originate here |
| amber HAS | [../amber_has/amber_has_index.md](../amber_has/amber_has_index.md) | architecture specification this MAS implements |
| amber Pre-HAS | [../amber_has/amber_prehas.md](../amber_has/amber_prehas.md) | original feature sketches |
| K-map / signal-contract workbook | [../gen_amber_contracts_kmaps.py](../gen_amber_contracts_kmaps.py) | combinational-contract sheets and kmaps |
| jet PRD | [../../../jet-mesi-l1/PRD.md](../../../jet-mesi-l1/PRD.md) | lockup-free follow-on; amber must not pre-decide jet's J-rows |
| onyx PRD | [../../../onyx-ace-ccu/PRD.md](../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the ACE-shaped snoop port; onyx D2 defines the coherent-transaction subset |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| gem5 Ruby protocols | [../../../References/gem5-ruby-protocols/README.md](../../../References/gem5-ruby-protocols/README.md) | golden-protocol source for the Python reference model and FSM oracles |
| cache simulator | [../../../../../../bin/apps/cache_sim/README.md](../../../../../../bin/apps/cache_sim/README.md) | golden parity model for LRU/FIFO/RANDOM |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

---

**Last Updated:** 2026-10-06
**Maintained By:** amber architecture
