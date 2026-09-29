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

# RAPIDS Beats Architecture MAS

**Version:** 0.7
**Date:** 2026-07-13
**Purpose:** Module Architecture Specification for RAPIDS Phase 1 "Beats" Architecture

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture Overview](ch01_overview/01_architecture.md)
- [Top-Level Port List](ch01_overview/02_port_list.md)
- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### Chapter 2: FUB (Functional Unit Blocks)

**Control Path:**
- [Scheduler](ch02_fub_blocks/01_scheduler.md)
- [Descriptor Engine](ch02_fub_blocks/02_descriptor_engine.md)

**AXI Engines:**
- [AXI Read Engine](ch02_fub_blocks/03_axi_read_engine.md)
- [AXI Write Engine](ch02_fub_blocks/04_axi_write_engine.md)

**Flow Control:**
- [Beats Alloc Control](ch02_fub_blocks/05_beats_alloc_ctrl.md)
- [Beats Drain Control](ch02_fub_blocks/06_beats_drain_ctrl.md)
- [Beats Latency Bridge](ch02_fub_blocks/07_beats_latency_bridge.md)

**Control Engines:**
- [Control-Read Engine](ch02_fub_blocks/08_ctrlrd_engine.md)
- [Control-Write Engine](ch02_fub_blocks/09_ctrlwr_engine.md)

### Chapter 3: Macro (Integration Blocks)

**Scheduler Integration:**
- [Beats Scheduler Group](ch03_macro_blocks/01_beats_scheduler_group.md)
- [Beats Scheduler Group Array](ch03_macro_blocks/02_beats_scheduler_group_array.md)

**Sink Data Path (Network to Memory):**
- [Sink Data Path](ch03_macro_blocks/03_sink_data_path.md)
- [Sink Data Path AXIS](ch03_macro_blocks/04_sink_data_path_axis.md)
- [Sink SRAM Controller](ch03_macro_blocks/05_snk_sram_controller.md)

**Source Data Path (Memory to Network):**
- [Source Data Path](ch03_macro_blocks/06_source_data_path.md)
- [Source Data Path AXIS](ch03_macro_blocks/07_source_data_path_axis.md)
- [Source SRAM Controller](ch03_macro_blocks/08_src_sram_controller.md)

**Top-Level Integration:**
- [RAPIDS Core Beats](ch03_macro_blocks/09_rapids_core_beats.md)
- [RAPIDS Registers](ch03_macro_blocks/10_rapids_regs.md)
- [RAPIDS Config Block](ch03_macro_blocks/11_rapids_config_block.md)
- [RAPIDS Beats Top](ch03_macro_blocks/12_rapids_beats_top.md)

### Chapter 4: Interfaces

- [Interface Overview](ch04_interfaces/README.md)
- [AXI4 Interface Specification](ch04_interfaces/01_axi4_interface_spec.md)
- [AXIS Interface Specification](ch04_interfaces/02_axis_interface_spec.md)
- [MonBus Interface Specification](ch04_interfaces/03_monbus_interface_spec.md)

---

## Quick Reference

### FUB Modules (fub_beats/)

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| scheduler_beats | `scheduler_beats.sv` | Transfer coordinator, descriptor processing | Implemented |
| descriptor_engine_beats | `descriptor_engine_beats.sv` | Descriptor fetch/parse (256-bit) | Implemented |
| axi_read_engine_beats | `axi_read_engine_beats.sv` | AXI read master, streaming pipeline | Implemented |
| axi_write_engine_beats | `axi_write_engine_beats.sv` | AXI write master, streaming pipeline | Implemented |
| alloc_ctrl_beats | `alloc_ctrl_beats.sv` | Space allocation tracking (virtual FIFO); kept and tested, no longer in the SRAM path since `bdf4e0dff` | Implemented |
| drain_ctrl_beats | `drain_ctrl_beats.sv` | Data availability tracking (virtual FIFO); kept and tested, no longer in the SRAM path | Implemented |
| latency_bridge_beats | `latency_bridge_beats.sv` | Registered-FIFO to valid/ready skid bridge; kept and tested, no longer in the SRAM path | Implemented |
| ctrlrd_engine | `ctrlrd_engine.sv` | Control-read consumer gate (poll-until-match, retry budget) | Implemented |
| ctrlwr_engine | `ctrlwr_engine.sv` | Control-write producer doorbell (single-beat write) | Implemented |

: FUB Module Summary

### Macro Modules (macro_beats/)

| Module | File | Purpose | Status |
|--------|------|---------|--------|
| scheduler_group_beats | `scheduler_group_beats.sv` | Scheduler + Descriptor Engine wrapper | Implemented |
| scheduler_group_array_beats | `scheduler_group_array_beats.sv` | 8-channel scheduler array with arbitration | Implemented |
| snk_data_path_beats | `snk_data_path_beats.sv` | Network-to-memory path integration | Implemented |
| snk_data_path_axis_beats | `snk_data_path_axis_beats.sv` | AXIS variant of sink path | Implemented |
| src_data_path_beats | `src_data_path_beats.sv` | Memory-to-network path integration | Implemented |
| src_data_path_axis_beats | `src_data_path_axis_beats.sv` | AXIS variant of source path | Implemented |
| snk_sram_controller_beats | `snk_sram_controller_beats.sv` | Sink SRAM: naming wrapper around STREAM's `sram_controller` (one instance, per-channel FIFOs inside it) | Implemented |
| src_sram_controller_beats | `src_sram_controller_beats.sv` | Source SRAM: naming wrapper around STREAM's `sram_controller` | Implemented |
| rapids_src_beats / rapids_snk_beats | `rapids_src_beats.sv`, `rapids_snk_beats.sv` | One half each: scheduler array + data path + monbus merge | Implemented |
| rapids_core_beats | `rapids_core_beats.sv` | Both halves + the core monbus arbiter | Implemented |
| rapids_regs | `regs/generated/rtl/rapids_regs.sv` (generated from `rtl/macro_beats/rapids_regs.rdl`) | PeakRDL register block (base + MON regfile @ 0x1000) | Implemented |
| rapids_config_block | `rapids_config_block.sv` | Maps register `hwif_out` to core/monitor `cfg_*` | Implemented |
| rapids_beats_top | `rapids_beats_top.sv` | Top-level: APB slave, kickoff, monitors, MonBus AXI-Lite group | Implemented |

: Macro Module Summary

---

## Architecture Comparison: RAPIDS vs STREAM

The "beats" architecture is a Phase 1 implementation of RAPIDS that shares concepts with STREAM but targets network-to-memory (and vice versa) transfers rather than memory-to-memory.

| Feature | STREAM | RAPIDS Beats |
|---------|--------|--------------|
| **Primary Use** | Memory-to-memory DMA | Network-to-memory accelerator |
| **Data Paths** | Single bidirectional | Separate sink/source paths |
| **Network Interface** | None | AXIS master/slave |
| **SRAM Buffering** | Shared buffer | Separate sink/source buffers |
| **Descriptor Format** | 256-bit | 256-bit (compatible) |
| **Channel Count** | 8 | 8 |
| **Flow Control** | alloc_ctrl/drain_ctrl | STREAM `stream_alloc_ctrl`/`stream_drain_ctrl` inside the shared `sram_controller` (`alloc_ctrl_beats`/`drain_ctrl_beats` kept, out of the path) |

: RAPIDS Beats vs STREAM Comparison

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

**See:** [Clocks and Reset](ch01_overview/03_clocks_and_reset.md) for complete timing specifications

---

## Interface Summary

### External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| AXI4 (Descriptor) | Master | 256-bit | Descriptor fetch |
| AXI4 (Sink Write) | Master | 512-bit (param) | Sink data write to memory |
| AXI4 (Source Read) | Master | 512-bit (param) | Source data read from memory |
| AXIS (Sink) | Slave | 512-bit (param) | Network data ingress |
| AXIS (Source) | Master | 512-bit (param) | Network data egress |
| MonBus | Master | 64-bit | Monitor packet output |

: External Interfaces

### Internal Buses

| Interface | Width | Purpose |
|-----------|-------|---------|
| MonBus | 64-bit | Internal monitoring bus |
| Descriptor Bus | 256-bit | Descriptor distribution |
| SRAM Data Bus | 512-bit | SRAM read/write data |

: Internal Buses

---

## Related Documentation

- **[PRD.md](../../PRD.md)** - Product requirements and overview
- **[CLAUDE.md](../../CLAUDE.md)** - AI development guide
- **[RAPIDS Beats HAS](../rapids_beats_has/rapids_beats_has_index.md)** - Architecture specification (the original pre-beats rapids_spec/ tree was retired)

---

## Specification Conventions

### Signal Naming

- **Clock:** `aclk`
- **Reset:** `aresetn` (active-low)
- **Valid/Ready:** Standard AXI/AXIS handshake
- **Registers:** `r_` prefix (e.g., `r_state`, `r_counter`)
- **Wires:** `w_` prefix (e.g., `w_next_state`, `w_grant`)

### Parameter Naming

- **Uppercase:** `NUM_CHANNELS`, `DATA_WIDTH`, `ADDR_WIDTH`
- **Derived:** `CHAN_WIDTH = $clog2(NUM_CHANNELS)`

### Figure and Table Numbering

- **Figures:** `Figure X.Y.Z: Title` where X=chapter, Y=section, Z=figure number
- **Tables:** Caption line `: Table Title` after table markdown

---

**Last Updated:** 2026-07-13
**Maintained By:** RAPIDS Architecture Team
