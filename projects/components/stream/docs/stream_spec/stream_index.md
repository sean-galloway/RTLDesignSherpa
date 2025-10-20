# STREAM Specification Index

**Version:** 0.26
**Date:** 2025-10-17
**Purpose:** Complete technical specification for STREAM subsystem

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Chapter 1: Overview

- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### Chapter 2: Functional Blocks

- [Descriptor Engine](ch02_blocks/01_01_descriptor_engine.md)
- [Scheduler](ch02_blocks/01_02_scheduler.md)
- [AXI Read Engine](ch02_blocks/02_01_axi_read_engine.md)
- [AXI Write Engine](ch02_blocks/02_02_axi_write_engine.md)
- [SRAM Controller](ch02_blocks/03_sram_controller.md)
- [Simple SRAM](ch02_blocks/04_simple_sram.md)
- [Channel Arbiter](ch02_blocks/05_channel_arbiter.md)
- [APB Config](ch02_blocks/06_apb_config.md)
- [MonBus AXIL Group](ch02_blocks/07_monbus_axil_group.md)
- [Top-Level Integration](ch02_blocks/08_stream_top.md)
- [Performance Profiler](ch02_blocks/09_perf_profiler.md)

---

## Quick Reference

### Functional Unit Blocks (FUB)

| Module | File | Purpose | Lines | Status |
|--------|------|---------|-------|--------|
| descriptor_engine | `stream_fub/descriptor_engine.sv` | Descriptor fetch/parse (256-bit) | ~300 | [Done] Simplified from RAPIDS |
| scheduler | `stream_fub/scheduler.sv` | Transfer coordinator | ~400 | [Done] Created (corrected) |
| axi_read_engine | `stream_fub/axi_read_engine.sv` | AXI read master | ~350 | [Done] Created (no FSM - streaming pipeline) |
| axi_write_engine | `stream_fub/axi_write_engine.sv` | AXI write master | ~400 | [Done] Created (no FSM - streaming pipeline) |
| sram_controller | `stream_fub/sram_controller.sv` | Per-channel buffer management | ~350 | [Done] Created (no FSM - pointer arithmetic + pre-allocation) |
| simple_sram | `stream_fub/simple_sram.sv` | Dual-port SRAM primitive | ~150 | [Done] Copied from RAPIDS |
| perf_profiler | `stream_fub/perf_profiler.sv` | Channel performance profiling | ~400 | [Done] Dual-mode timestamp/elapsed tracking |

### Integration Blocks (MAC)

| Module | File | Purpose | Lines | Status |
|--------|------|---------|-------|--------|
| channel_arbiter | `stream_macro/channel_arbiter.sv` | Priority arbitration | ~200 | [Pending] To be created |
| apb_config | `regs/stream_regs.rdl` + wrapper | Config registers | ~350 | [Future] PeakRDL-based |
| monbus_axil_group | `stream_macro/monbus_axil_group.sv` | MonBus + AXIL | ~800 | [Done] Copied from RAPIDS |
| stream_top | `stream_macro/stream_top.sv` | Top-level | ~500 | [Pending] To be created |

---

## Performance Modes (AXI Engines)

STREAM AXI engines support three performance modes via compile-time parameters:

### Low Performance Mode
- **Target:** Area-optimized, low throughput
- **Features:** Minimal logic, single outstanding transaction
- **Use Case:** Tutorial examples, area-constrained designs
- **Area:** ~250 LUTs per engine

### Medium Performance Mode
- **Target:** Balanced area/performance
- **Features:** Basic pipelining, 2-4 outstanding transactions
- **Use Case:** Typical FPGA implementations
- **Area:** ~400 LUTs per engine

### High Performance Mode
- **Target:** Maximum throughput
- **Features:** Full pipelining, 8+ outstanding transactions
- **Use Case:** High-bandwidth ASIC implementations
- **Area:** ~600 LUTs per engine

---

## Clock and Reset Summary

### Clock Domains

| Clock | Frequency | Usage |
|-------|-----------|-------|
| `aclk` | 100-500 MHz | Primary - all STREAM logic, AXI/AXIL interfaces |
| `pclk` | 50-200 MHz | APB configuration interface (may be async to aclk) |

### Reset Signals

| Reset | Polarity | Type | Usage |
|-------|----------|------|-------|
| `aresetn` | Active-low | Async assert, sync deassert | Primary - all STREAM logic |
| `presetn` | Active-low | Async assert, sync deassert | APB configuration interface |

**See:** [Clocks and Reset](ch01_overview/03_clocks_and_reset.md) for complete timing specifications

---

## Interface Summary

### External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| APB | Slave | 32-bit | Configuration registers |
| AXI (Descriptor) | Master | 256-bit | Descriptor fetch |
| AXI (Read) | Master | 512-bit (param) | Source data read |
| AXI (Write) | Master | 512-bit (param) | Destination data write |
| AXIL (Slave) | Slave | 32-bit | Error/interrupt FIFO access |
| AXIL (Master) | Master | 32-bit | MonBus packet logging to memory |
| IRQ | Output | 1-bit | Error interrupt |

### Internal Buses

| Interface | Width | Purpose |
|-----------|-------|---------|
| MonBus | 64-bit | Internal monitoring bus (channels -> monbus_axil_group) |

---

## Area Estimates

### By Performance Mode

| Configuration | Total LUTs | SRAM | Use Case |
|--------------|------------|------|----------|
| Low (Tutorial) | ~9,500 | 64 KB | Educational, area-constrained |
| Medium (Typical) | ~11,200 | 64 KB | Balanced FPGA implementations |
| High (Performance) | ~13,700 | 64 KB | High-throughput ASIC/FPGA |

### Breakdown (Low Performance)

| Component | Instances | Area/Instance | Total |
|-----------|-----------|---------------|-------|
| Descriptor Engine | 8 | ~300 LUTs | ~2,400 LUTs |
| Scheduler | 8 | ~400 LUTs | ~3,200 LUTs |
| AXI Read Engine (Low) | 1 | ~250 LUTs | ~250 LUTs |
| AXI Write Engine (Low) | 1 | ~250 LUTs | ~250 LUTs |
| SRAM Controller | 1 | ~1,600 LUTs | ~1,600 LUTs |
| Simple SRAM (internal) | 1-8 | 1024x64B total | 64 KB |
| Channel Arbiter | 3 | ~150 LUTs | ~450 LUTs |
| APB Config | 1 | ~350 LUTs | ~350 LUTs |
| MonBus AXIL Group | 1 | ~1,000 LUTs | ~1,000 LUTs |
| **Total** | - | - | **~9,500 LUTs + 64KB** |

---

## Related Documentation

- **[PRD.md](../../PRD.md)** - Product requirements and overview
- **[ARCHITECTURAL_NOTES.md](../ARCHITECTURAL_NOTES.md)** - Critical design decisions
- **[CLAUDE.md](../../CLAUDE.md)** - AI development guide
- **[Register Generation](../../regs/README.md)** - PeakRDL workflow

---

## Specification Conventions

### Signal Naming

- **Clock:** `aclk`, `pclk`
- **Reset:** `aresetn`, `presetn` (active-low)
- **Valid/Ready:** Standard AXI/custom handshake
- **Registers:** `r_` prefix (e.g., `r_state`, `r_counter`)
- **Wires:** `w_` prefix (e.g., `w_next_state`, `w_grant`)

### Parameter Naming

- **Uppercase:** `NUM_CHANNELS`, `DATA_WIDTH`, `ADDR_WIDTH`
- **String parameters:** `PERFORMANCE` ("LOW", "MEDIUM", "HIGH")

### State Machine Naming

```systemverilog
typedef enum logic [3:0] {
    IDLE   = 4'h0,
    ACTIVE = 4'h1,
    // ...
} state_t;

state_t r_state, w_next_state;  // Current and next state
```

---

**Last Updated:** 2025-10-17
**Maintained By:** STREAM Architecture Team
