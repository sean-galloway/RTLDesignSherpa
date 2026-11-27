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

# onyx MAS Index

**Version:** 0.1
**Date:** 2026-11-27
**Purpose:** Micro-architecture specification for the onyx snoop-based ACE
coherency unit
**Scope:** Cycle-level behavior, per-block micro-architecture, and signal
contracts for `onyx_ccu` (the manager, one module) and `onyx_top` (the
manager with its MonBus observer and exact counters). The binding
architecture lives in the [onyx HAS](../onyx_has/onyx_has_index.md); the
D and N rulings are recorded in the [onyx PRD](../../PRD.md).

**Status:** written against the RTL as built (onyx TASK-001, through the
D1 IO port, the D9 observer with its mask layers and address window, and
the BUG-001..003 fixes). Where this book and the RTL disagree, the RTL is
right and this book is wrong.

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture and What the MAS Covers](ch01_overview/01_architecture.md)
- [Top-Level Port List](ch01_overview/02_port_list.md)
- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### Chapter 2: Functional Blocks

- [Front End: Pending Queues and the AR Take](ch02_blocks/01_front_end.md)
- [Transaction Table, Grant and the Per-Line Lock](ch02_blocks/02_table_grant_lock.md)
- [Snoop Fanout and Response Gather](ch02_blocks/03_fanout_gather.md)
- [Memory Read Path: AR Stage, Hold and R Router](ch02_blocks/04_memory_read.md)
- [Snoop-Data Buffers and Replay Engines](ch02_blocks/05_buffers_replay.md)
- [Write Port and Write-Back Order](ch02_blocks/06_write_port.md)
- [ACE-Lite IO Port](ch02_blocks/07_io_port.md)
- [onyx_top: the Wrapper](ch02_blocks/08_onyx_top.md)

### Chapter 3: Interfaces

- [Cache-Side Port Timing](ch03_interfaces/01_cache_side.md)
- [Snoop AC / CR / CD Timing](ch03_interfaces/02_snoop_channels.md)
- [Memory-Side AXI4 Master Timing](ch03_interfaces/03_memory_master.md)
- [Event Taps and Debug Taps](ch03_interfaces/04_event_taps.md)

### Chapter 4: MonBus Observation

- [Event Classes and Payloads](ch04_monbus_observation/01_event_map.md)
- [Holders, Drop-and-Count and the Mask Layers](ch04_monbus_observation/02_observer.md)
- [onyx_counters](ch04_monbus_observation/03_counters.md)

### Chapter 5: Verification

- [Formal Targets](ch05_verification/01_formal_targets.md)
- [DV Rigs](ch05_verification/02_dv_rigs.md)

### Chapter 6: Configuration

- [Elaboration Parameters and Built Configurations](ch06_configuration/01_elaboration_configs.md)

## Figures

| Figure | Source | Subject |
|---|---|---|
| 1.1 | `assets/graphviz/01_whole_unit.dot` | the whole unit as built; a copy of the HAS Figure 2.1 source, kept in step (each book build reads only its own assets) |
| 2.6 | `assets/graphviz/02_write_port.dot` | the write port: candidates, holds, the round-robin and the burst FSM |

: Table 0.0: Figures and their sources

## Quick Reference

| Module | File | Role |
|---|---|---|
| `onyx_ccu` | `rtl/top/onyx_ccu.sv` | the manager: front end, table, fanout and gather, memory master, buffers and replay, write port, IO port, event taps |
| `onyx_top` | `rtl/top/onyx_top.sv` | `onyx_ccu` + `onyx_monlite` + `onyx_counters`, one MonBus output |
| `onyx_monlite` | `rtl/fub/onyx_monlite.sv` | drop-and-count MonBus observer on the event taps (D9) |
| `onyx_counters` | `rtl/fub/onyx_counters.sv` | eight exact 32-bit saturating event counters |
| `onyx_pkg` | `rtl/includes/onyx_pkg.sv` | event codes `0x20`-`0x27`, the IO grant classes, the monitor ids |
| `l1_pkg` | `cache-ip/common-ip/rtl/includes/l1_pkg.sv` | geometry defaults, the `AMBER_ACE_*` request classes, CRRESP bit positions (shared with the caches) |

: Table 0.1: onyx modules

Filelists: `rtl/filelists/onyx_ccu.f`, `onyx_top.f`, `onyx_monlite.f`,
`onyx_counters.f`, `onyx_pkg.f`; `onyx_top.f` includes the other three
module lists.

## Related Documentation

| Document | Where | Relationship |
|---|---|---|
| onyx PRD | [../../PRD.md](../../PRD.md) | **binding requirements**: the D and N rows and success criteria |
| onyx HAS | [../onyx_has/onyx_has_index.md](../onyx_has/onyx_has_index.md) | the architecture this MAS implements |
| onyx TASK-001 | `vault/tracking/projects/components/cache-ip/onyx-ace-ccu/task/active/TASK-001.md` | the build log: every measured result and proof run, with dates |
| jet-prime pair fabric | `cache-ip/jet-prime-mesi-l1/rtl/` (`jet_prime_pair_fabric`) | the two-port manager onyx generalizes |
| AMBA ACE Interface Definition | [../../../References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| Handbook: block diagrams | `vault/handbook/authoring/block-diagrams.md` | the figure style |
| Handbook: MonBus | `vault/handbook/design/monbus-is-a-low-bandwidth-channel.md` | why the observer carries mask layers and a window |
| Global Requirements | [../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

**Last Updated:** 2026-11-27
**Maintained By:** onyx architecture
