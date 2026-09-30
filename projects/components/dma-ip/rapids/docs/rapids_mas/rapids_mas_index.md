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

# RAPIDS Architecture MAS

**Version:** 0.1
**Date:** 2026-09-30
**Purpose:** Module Architecture Specification for byte-granular RAPIDS, the product design that succeeds the RAPIDS Beats stepping stone

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

Chapters marked **(shared with RAPIDS Beats)** are the RAPIDS Beats MAS
chapters, linked rather than copied: the two designs share them exactly.
Where such a chapter names a module, the byte-granular module is the same
name without the `_beats` suffix (`rapids_top` for `rapids_beats_top`,
`scheduler` for `scheduler_beats`). The byte-granular RTL lives in `fub/` and
`macro/`; the Beats RTL stays in `fub_beats/` and `macro_beats/`.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture Overview](ch01_overview/01_architecture.md)
- [Top-Level Port List](../rapids_beats_mas/ch01_overview/02_port_list.md) (shared with RAPIDS Beats)
- [Clocks and Reset](../rapids_beats_mas/ch01_overview/03_clocks_and_reset.md) (shared with RAPIDS Beats)

### Chapter 2: FUB (Functional Unit Blocks)

**Control Path:**
- [Scheduler](ch02_fub_blocks/01_scheduler.md)
- [Descriptor Engine](../rapids_beats_mas/ch02_fub_blocks/02_descriptor_engine.md) (shared with RAPIDS Beats)

**AXI Engines:**
- [AXI Read Engine](ch02_fub_blocks/03_axi_read_engine.md)
- [AXI Write Engine](ch02_fub_blocks/04_axi_write_engine.md)

**Flow Control:**
- [Beats Alloc Control](../rapids_beats_mas/ch02_fub_blocks/05_beats_alloc_ctrl.md) (shared with RAPIDS Beats)
- [Beats Drain Control](../rapids_beats_mas/ch02_fub_blocks/06_beats_drain_ctrl.md) (shared with RAPIDS Beats)
- [Beats Latency Bridge](../rapids_beats_mas/ch02_fub_blocks/07_beats_latency_bridge.md) (shared with RAPIDS Beats)

**Control Engines:**
- [Control-Read Engine](../rapids_beats_mas/ch02_fub_blocks/08_ctrlrd_engine.md) (shared with RAPIDS Beats)
- [Control-Write Engine](../rapids_beats_mas/ch02_fub_blocks/09_ctrlwr_engine.md) (shared with RAPIDS Beats)

### Chapter 3: Macro (Integration Blocks)

**Scheduler Integration:**
- [Scheduler Group](ch03_macro_blocks/01_scheduler_group.md)
- [Scheduler Group Array](ch03_macro_blocks/02_scheduler_group_array.md)

**Sink Data Path (Network to Memory):**
- [Sink Data Path](ch03_macro_blocks/03_snk_data_path.md)
- [Sink Data Path AXIS](ch03_macro_blocks/04_snk_data_path_axis.md)
- [Sink SRAM Controller](../rapids_beats_mas/ch03_macro_blocks/05_snk_sram_controller.md) (shared with RAPIDS Beats)

**Source Data Path (Memory to Network):**
- [Source Data Path](../rapids_beats_mas/ch03_macro_blocks/06_source_data_path.md) (shared with RAPIDS Beats)
- [Source Data Path AXIS](ch03_macro_blocks/07_src_data_path_axis.md)
- [Source SRAM Controller](../rapids_beats_mas/ch03_macro_blocks/08_src_sram_controller.md) (shared with RAPIDS Beats)

**Top-Level Integration:**
- [RAPIDS Core, Sink Half and Source Half](ch03_macro_blocks/09_rapids_core.md)
- [RAPIDS Registers](../rapids_beats_mas/ch03_macro_blocks/10_rapids_regs.md) (shared with RAPIDS Beats)
- [RAPIDS Config Block](../rapids_beats_mas/ch03_macro_blocks/11_rapids_config_block.md) (shared with RAPIDS Beats)
- [RAPIDS Top](ch03_macro_blocks/12_rapids_top.md)

### Chapter 4: Interfaces

- [AXI4 Interface Specification](ch04_interfaces/01_axi4_interface_spec.md)
- [AXIS Interface Specification](ch04_interfaces/02_axis_interface_spec.md)
- [MonBus Interface Specification](../rapids_beats_mas/ch04_interfaces/03_monbus_interface_spec.md) (shared with RAPIDS Beats)
- [Packet Record Interface Specification](ch04_interfaces/04_packet_record_interface_spec.md)

---

## Quick Reference

### FUB Modules (fub/)

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| scheduler | `scheduler.sv` | Transfer coordinator; byte-to-beat math and packet records | Implemented |
| descriptor_engine | `descriptor_engine.sv` | Descriptor fetch/parse (256-bit); same as Beats | Implemented |
| axi_read_engine | `axi_read_engine.sv` | AXI read master; 4 KB burst cap, aligned ARADDR | Implemented |
| axi_write_engine | `axi_write_engine.sv` | AXI write master; WSTRB input, 4 KB burst cap | Implemented |
| alloc_ctrl / drain_ctrl / latency_bridge | (Beats modules) | Kept and tested; not in the SRAM path | Shared with Beats |
| ctrlrd_engine | `ctrlrd_engine.sv` | Control-read consumer gate; same as Beats | Implemented |
| ctrlwr_engine | `ctrlwr_engine.sv` | Control-write producer doorbell; same as Beats | Implemented |

: FUB Module Summary

### Macro Modules (macro/)

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| scheduler_group | `scheduler_group.sv` | Scheduler + Descriptor Engine wrapper; packet-record ports | Implemented |
| scheduler_group_array | `scheduler_group_array.sv` | 8-channel scheduler array with arbitration; per-channel packet-record ports | Implemented |
| snk_data_path | `snk_data_path.sv` | Sink path integration; SRAM entry is `{strb, data}` | Implemented |
| snk_data_path_axis | `snk_data_path_axis.sv` | AXIS ingress shifter, packet records, length check | Implemented |
| src_data_path | `src_data_path.sv` | Source path integration; same as Beats | Shared with Beats |
| src_data_path_axis | `src_data_path_axis.sv` | AXIS egress shifter, one packet per descriptor | Implemented |
| snk_sram_controller / src_sram_controller | (Beats modules) | Shared `sram_controller` wrappers; width is a parameter | Shared with Beats |
| rapids_src / rapids_snk | `rapids_src.sv`, `rapids_snk.sv` | One half each; carry the packet-record nets | Implemented |
| rapids_core | `rapids_core.sv` | Both halves + the core monbus arbiter | Implemented |
| rapids_regs | (Beats register block) | PeakRDL register block; unchanged | Shared with Beats |
| rapids_config_block | (Beats module) | Maps register `hwif_out` to `cfg_*`; unchanged | Shared with Beats |
| rapids_top | `top/rapids_top.sv` | Top-level: APB slave, kickoff, monitors, MonBus AXI-Lite group | Implemented |

: Macro Module Summary

---

## What Differs from RAPIDS Beats

| Area | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| Descriptor length | beats | bytes (same 32-bit field) |
| Addresses | multiples of `DATA_WIDTH/8` | any byte, linear descriptors |
| Scheduler | loads `length` as the beat count | derives beats from offset and length; emits packet records |
| AXI engines | no burst cap, no WSTRB | 4 KB burst cap, aligned address, WSTRB input on write |
| Sink SRAM entry | `DATA_WIDTH` | `DATA_WIDTH + DATA_WIDTH/8` (`{strb, data}`) |
| Sink AXIS | one packet per drain block; no length check | ingress shifter, spill flush, length check |
| Source AXIS | full beats, packet per drain block | egress shifter, partial last beat, one packet per descriptor |
| TYPE=EXT | beat rows | beat rows (aligned addresses, beat-multiple lengths, permanent) |
| Ports | | new `sched_*_pkt_*` ports through group, array, core |

: RAPIDS versus RAPIDS Beats (MAS level)

---

## Architecture Comparison: RAPIDS vs STREAM

| Feature | STREAM | RAPIDS |
|---------|--------|--------|
| **Primary Use** | Memory-to-memory DMA | Network-to-memory and memory-to-network |
| **Data Paths** | Single bidirectional | Separate sink/source paths |
| **Network Interface** | None | AXIS master/slave with byte enables |
| **SRAM Buffering** | Shared buffer | Separate sink/source buffers |
| **Descriptor Format** | 256-bit | 256-bit (compatible) |
| **Channel Count** | 8 | 8 |
| **Granularity** | beats | bytes (linear descriptors) |

: RAPIDS vs STREAM Comparison

---

## Clock and Reset Summary

### Clock Domains

| Clock | Frequency | Usage |
|-------|-----------|-------|
| `aclk` | 100-500 MHz | Primary - all RAPIDS logic, AXI/AXIS interfaces |

: Clock Domains

### Reset Signals

| Reset | Polarity | Type | Usage |
|-------|----------|------|-------|
| `aresetn` | Active-low | Async assert, sync deassert | Primary - all RAPIDS logic |

: Reset Signals

**See:** [Clocks and Reset](../rapids_beats_mas/ch01_overview/03_clocks_and_reset.md) for complete timing specifications

---

## Interface Summary

### External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| AXI4 (Descriptor) | Master | 256-bit | Descriptor fetch |
| AXI4 (Sink Write) | Master | `DATA_WIDTH` (256 on the board; 512 default) | Sink data write to memory, with WSTRB |
| AXI4 (Source Read) | Master | `DATA_WIDTH` | Source data read from memory |
| AXIS (Sink) | Slave | `DATA_WIDTH` | Network data ingress, TSTRB honoured |
| AXIS (Source) | Master | `DATA_WIDTH` | Network data egress, TSTRB driven |
| MonBus | Master | 64-bit | Monitor packet output |

: External Interfaces

### Internal Buses

| Interface | Width | Purpose |
|-----------|-------|---------|
| MonBus | 64-bit | Internal monitoring bus |
| Descriptor Bus | 256-bit | Descriptor distribution |
| Sink SRAM Data Bus | `DATA_WIDTH + DATA_WIDTH/8` | `{strb, data}` per beat |
| Source SRAM Data Bus | `DATA_WIDTH` | Read data, aligned to memory lanes |
| Packet Record Bus | 32-bit bytes + `OFF_W` offset, per channel | One record per DATA descriptor |

: Internal Buses

---

## Related Documentation

- [RAPIDS Beats MAS](../rapids_beats_mas/rapids_beats_mas_index.md): the design this one builds on; shared chapters live there
- RAPIDS HAS: `../rapids_has/rapids_has_index.md`
- RAPIDS Beats HAS: `../rapids_beats_has/rapids_beats_has_index.md`

---

## Specification Conventions

- Tables are captioned after the table as `: Table N.M: title`.
- Figures are numbered `Figure N.M.K` with a `**Source:**` line.
- Waveforms are numbered `Waveform N.M`.
- Signal names in this book are RTL names. `OFF_W` is `$clog2(DATA_WIDTH/8)`; `BYTE_LANES` is `DATA_WIDTH/8`.
- A length is in bytes unless the text says beats.
